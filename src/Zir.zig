//! Zig Intermediate Representation. Astgen.zig converts AST nodes to these
//! untyped IR instructions. Next, Sema.zig processes these into AIR.
//! The minimum amount of information needed to represent a list of ZIR instructions.
//! Once this structure is completed, it can be used to generate AIR, followed by
//! machine code, without any memory access into the AST tree token list, node list,
//! or source bytes. Exceptions include:
//!  * Compile errors, which may need to reach into these data structures to
//!    create a useful report.
//!  * In the future, possibly inline assembly, which needs to get parsed and
//!    handled by the codegen backend, and errors reported there. However for now,
//!    inline assembly is not an exception.

const std = @import("std");
const builtin = @import("builtin");
const mem = std.mem;
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const BigIntConst = std.math.big.int.Const;
const BigIntMutable = std.math.big.int.Mutable;
const Ast = std.zig.Ast;

const Zir = @This();
const Type = @import("type.zig").Type;
const Value = @import("value.zig").Value;
const TypedValue = @import("TypedValue.zig");
const Module = @import("Module.zig");
const LazySrcLoc = Module.LazySrcLoc;

instructions: std.MultiArrayList(Inst).Slice,
/// In order to store references to strings in fewer bytes, we copy all
/// string bytes into here. String bytes can be null. It is up to whomever
/// is referencing the data here whether they want to store both index and length,
/// thus allowing null bytes, or store only index, and use null-termination. The
/// `string_bytes` array is agnostic to either usage.
/// Indexes 0 and 1 are reserved for special cases.
string_bytes: []u8,
/// The meaning of this data is determined by `Inst.Tag` value.
/// The first few indexes are reserved. See `ExtraIndex` for the values.
extra: []u32,

/// The data stored at byte offset 0 when ZIR is stored in a file.
pub const Header = extern struct {
    instructions_len: u32,
    string_bytes_len: u32,
    extra_len: u32,
    /// We could leave this as padding, however it triggers a Valgrind warning because
    /// we read and write undefined bytes to the file system. This is harmless, but
    /// it's essentially free to have a zero field here and makes the warning go away,
    /// making it more likely that following Valgrind warnings will be taken seriously.
    unused: u32 = 0,
    stat_inode: std.fs.File.INode,
    stat_size: u64,
    stat_mtime: i128,
};

pub const ExtraIndex = enum(u32) {
    /// If this is 0, no compile errors. Otherwise there is a `CompileErrors`
    /// payload at this index.
    compile_errors,
    /// If this is 0, this file contains no imports. Otherwise there is a `Imports`
    /// payload at this index.
    imports,

    _,
};

/// Returns the requested data, as well as the new index which is at the start of the
/// trailers for the object.
pub fn extraData(code: Zir, comptime T: type, index: usize) struct { data: T, end: usize } {
    const fields = @typeInfo(T).Struct.fields;
    var i: usize = index;
    var result: T = undefined;
    inline for (fields) |field| {
        @field(result, field.name) = switch (field.type) {
            u32 => code.extra[i],
            Inst.Ref => @intToEnum(Inst.Ref, code.extra[i]),
            i32 => @bitCast(i32, code.extra[i]),
            Inst.Call.Flags => @bitCast(Inst.Call.Flags, code.extra[i]),
            Inst.BuiltinCall.Flags => @bitCast(Inst.BuiltinCall.Flags, code.extra[i]),
            Inst.SwitchBlock.Bits => @bitCast(Inst.SwitchBlock.Bits, code.extra[i]),
            Inst.FuncFancy.Bits => @bitCast(Inst.FuncFancy.Bits, code.extra[i]),
            else => @compileError("bad field type"),
        };
        i += 1;
    }
    return .{
        .data = result,
        .end = i,
    };
}

/// Given an index into `string_bytes` returns the null-terminated string found there.
pub fn nullTerminatedString(code: Zir, index: usize) [:0]const u8 {
    var end: usize = index;
    while (code.string_bytes[end] != 0) {
        end += 1;
    }
    return code.string_bytes[index..end :0];
}

pub fn refSlice(code: Zir, start: usize, len: usize) []Inst.Ref {
    const raw_slice = code.extra[start..][0..len];
    return @ptrCast([]Inst.Ref, raw_slice);
}

pub fn hasCompileErrors(code: Zir) bool {
    return code.extra[@enumToInt(ExtraIndex.compile_errors)] != 0;
}

pub fn deinit(code: *Zir, gpa: Allocator) void {
    code.instructions.deinit(gpa);
    gpa.free(code.string_bytes);
    gpa.free(code.extra);
    code.* = undefined;
}

/// ZIR is structured so that the outermost "main" struct of any file
/// is always at index 0.
pub const main_struct_inst: Inst.Index = 0;

/// These are untyped instructions generated from an Abstract Syntax Tree.
/// The data here is immutable because it is possible to have multiple
/// analyses on the same ZIR happening at the same time.
pub const Inst = union(enum(u8)) {
    const info = @typeInfo(Inst).Union;
    pub const Tag = info.tag_type.?;
    pub const Data = @Type(.{ .Union = .{
        .layout = .Auto,
        .tag_type = null,
        .fields = info.fields,
        .decls = &.{},
    } });

    /// Arithmetic addition, asserts no integer overflow.
    /// Payload is `Bin`.
    add: PayloadNode,
    /// Twos complement wrapping integer addition.
    /// Payload is `Bin`.
    addwrap: PayloadNode,
    /// Saturating addition.
    /// Payload is `Bin`.
    add_sat: PayloadNode,
    /// The same as `add` except no safety check.
    add_unsafe: PayloadNode,
    /// Arithmetic subtraction. Asserts no integer overflow.
    /// Payload is `Bin`.
    sub: PayloadNode,
    /// Twos complement wrapping integer subtraction.
    /// Payload is `Bin`.
    subwrap: PayloadNode,
    /// Saturating subtraction.
    /// Payload is `Bin`.
    sub_sat: PayloadNode,
    /// Arithmetic multiplication. Asserts no integer overflow.
    /// Payload is `Bin`.
    mul: PayloadNode,
    /// Twos complement wrapping integer multiplication.
    /// Payload is `Bin`.
    mulwrap: PayloadNode,
    /// Saturating multiplication.
    /// Payload is `Bin`.
    mul_sat: PayloadNode,
    /// Implements the `@divExact` builtin.
    /// Payload is `Bin`.
    div_exact: PayloadNode,
    /// Implements the `@divFloor` builtin.
    /// Payload is `Bin`.
    div_floor: PayloadNode,
    /// Implements the `@divTrunc` builtin.
    /// Payload is `Bin`.
    div_trunc: PayloadNode,
    /// Implements the `@mod` builtin.
    /// Payload is `Bin`.
    mod: PayloadNode,
    /// Implements the `@rem` builtin.
    /// Payload is `Bin`.
    rem: PayloadNode,
    /// Ambiguously remainder division or modulus. If the computation would possibly have
    /// a different value depending on whether the operation is remainder division or modulus,
    /// a compile error is emitted. Otherwise the computation is performed.
    /// Payload is `Bin`.
    mod_rem: PayloadNode,
    /// Integer shift-left. Zeroes are shifted in from the right hand side.
    /// Payload is `Bin`.
    shl: PayloadNode,
    /// Implements the `@shlExact` builtin.
    /// Payload is `Bin`.
    shl_exact: PayloadNode,
    /// Saturating shift-left.
    /// Payload is `Bin`.
    shl_sat: PayloadNode,
    /// Integer shift-right. Arithmetic or logical depending on the signedness of
    /// the integer type.
    /// Payload is `Bin`.
    shr: PayloadNode,
    /// Implements the `@shrExact` builtin.
    /// Payload is `Bin`.
    shr_exact: PayloadNode,

    /// Declares a parameter of the current function. Used for:
    /// * debug info
    /// * checking shadowing against declarations in the current namespace
    /// * parameter type expressions referencing other parameters
    /// These occur in the block outside a function body (the same block as
    /// contains the func instruction).
    /// Token is the parameter name, payload is a `Param`.
    param: PayloadToken,
    /// Same as `param` except the parameter is marked comptime.
    param_comptime: PayloadToken,
    /// Same as `param` except the parameter is marked anytype.
    /// Token is the parameter name. String is the parameter name.
    param_anytype: StringToken,
    /// Same as `param` except the parameter is marked both comptime and anytype.
    /// Token is the parameter name. String is the parameter name.
    param_anytype_comptime: StringToken,
    /// Array concatenation. `a ++ b`
    /// Payload is `Bin`.
    array_cat: PayloadNode,
    /// Array multiplication `a ** b`
    /// Payload is `Bin`.
    array_mul: PayloadNode,
    /// `[N]T` syntax. No source location provided.
    /// Payload is `Bin`. lhs is length, rhs is element type.
    array_type: PayloadNode,
    /// `[N:S]T` syntax. Source location is the array type expression node.
    /// Payload is `ArrayTypeSentinel`.
    array_type_sentinel: PayloadNode,
    /// `@Vector` builtin.
    /// Payload is `Bin`. lhs is length, rhs is element type.
    vector_type: PayloadNode,
    /// Given an indexable type, returns the type of the element at given index.
    /// lhs is the indexable type, rhs is the index.
    elem_type_index: Bin,
    /// Given a pointer to an indexable object, returns the len property. This is
    /// used by for loops. This instruction also emits a for-loop specific compile
    /// error if the indexable object is not indexable.
    /// The AST node is the for loop node.
    indexable_ptr_len: UnaryNode,
    /// Create a `anyframe->T` type.
    anyframe_type: UnaryNode,
    /// Type coercion. No source location attached.
    as: Bin,
    /// Type coercion to the function's return type.
    /// Payload is `As`. AST node could be many things.
    as_node: PayloadNode,
    /// Same as `as_node` but ignores runtime to comptime int error.
    as_shift_operand: PayloadNode,
    /// Bitwise AND. `&`
    bit_and: PayloadNode,
    /// Reinterpret the memory representation of a value as a different type.
    /// Payload is `Bin`.
    bitcast: PayloadNode,
    /// Bitwise NOT. `~`
    bit_not: UnaryNode,
    /// Bitwise OR. `|`
    bit_or: PayloadNode,
    /// A labeled block of code, which can return a value.
    /// Payload is `Block`.
    block: PayloadNode,
    /// Like `block`, but forces full evaluation of its contents at compile-time.
    /// Payload is `Block`.
    block_comptime: PayloadNode,
    /// A list of instructions which are analyzed in the parent context, without
    /// generating a runtime block. Must terminate with an "inline" variant of
    /// a noreturn instruction.
    /// Payload is `Block`.
    block_inline: PayloadNode,
    /// Implements `suspend {...}`.
    /// Payload is `Block`.
    suspend_block: PayloadNode,
    /// Boolean NOT. See also `bit_not`.
    bool_not: UnaryNode,
    /// Short-circuiting boolean `and`. `lhs` is a boolean `Ref` and the other operand
    /// is a block, which is evaluated if `lhs` is `true`.
    bool_br_and: BoolBreak,
    /// Short-circuiting boolean `or`. `lhs` is a boolean `Ref` and the other operand
    /// is a block, which is evaluated if `lhs` is `false`.
    bool_br_or: BoolBreak,
    /// Return a value from a block.
    /// Uses the source information from previous instruction.
    @"break": BreakNode,
    /// Return a value from a block. This instruction is used as the terminator
    /// of a `block_inline`. It allows using the return value from `Sema.analyzeBody`.
    /// This instruction may also be used when it is known that there is only one
    /// break instruction in a block, and the target block is the parent.
    break_inline: BreakNode,
    /// Checks that comptime control flow does not happen inside a runtime block.
    check_comptime_control_flow: UnaryNode,
    /// Function call.
    /// Payload is `Call`.
    /// AST node is the function call.
    call: PayloadNode,
    /// Implements the `@call` builtin.
    /// Payload is `BuiltinCall`.
    /// AST node is the builtin call.
    builtin_call: PayloadNode,
    /// `<`
    /// Payload is `Bin`.
    cmp_lt: PayloadNode,
    /// `<=`
    /// Payload is `Bin`.
    cmp_lte: PayloadNode,
    /// `==`
    /// Payload is `Bin`.
    cmp_eq: PayloadNode,
    /// `>=`
    /// Payload is `Bin`.
    cmp_gte: PayloadNode,
    /// `>`
    /// Payload is `Bin`.
    cmp_gt: PayloadNode,
    /// `!=`
    /// Payload is `Bin`.
    cmp_neq: PayloadNode,
    /// Coerces a result location pointer to a new element type. It is evaluated "backwards"-
    /// as type coercion from the new element type to the old element type.
    /// Payload is `Bin`.
    /// LHS is destination element type, RHS is result pointer.
    coerce_result_ptr: PayloadNode,
    /// Conditional branch. Splits control flow based on a boolean condition value.
    /// AST node is an if, while, for, etc.
    /// Payload is `CondBr`.
    condbr: PayloadNode,
    /// Same as `condbr`, except the condition is coerced to a comptime value, and
    /// only the taken branch is analyzed. The then block and else block must
    /// terminate with an "inline" variant of a noreturn instruction.
    condbr_inline: PayloadNode,
    /// Given an operand which is an error union, splits control flow. In
    /// case of error, control flow goes into the block that is part of this
    /// instruction, which is guaranteed to end with a return instruction
    /// and never breaks out of the block.
    /// In the case of non-error, control flow proceeds to the next instruction
    /// after the `try`, with the result of this instruction being the unwrapped
    /// payload value, as if `err_union_payload_unsafe` was executed on the operand.
    /// Payload is `Try`.
    @"try": PayloadNode,
    /// Same as `try` except the operand is a pointer and the result is a pointer.
    try_ptr: PayloadNode,
    /// An error set type definition. Contains a list of field names.
    /// Payload is `ErrorSetDecl`.
    error_set_decl: PayloadNode,
    error_set_decl_anon: PayloadNode,
    error_set_decl_func: PayloadNode,
    /// Declares the beginning of a statement. Used for debug info.
    /// The line and column are offset from the parent declaration.
    dbg_stmt: LineColumn,
    /// Marks a variable declaration. Used for debug info.
    /// The string is the local variable name,
    /// and the operand is the pointer to the variable's location. The local
    /// may be a const or a var.
    dbg_var_ptr: StringOperator,
    /// Same as `dbg_var_ptr` but the local is always a const and the operand
    /// is the local's value.
    dbg_var_val: StringOperator,
    /// Marks the beginning of a semantic scope for debug info variables.
    dbg_block_begin,
    /// Marks the end of a semantic scope for debug info variables.
    dbg_block_end,
    /// Uses a name to identify a Decl and takes a pointer to it.
    decl_ref: StringToken,
    /// Uses a name to identify a Decl and uses it as a value.
    decl_val: StringToken,
    /// Load the value from a pointer. Assumes `x.*` syntax.
    /// AST node is the `x.*` syntax.
    load: UnaryNode,
    /// Arithmetic division. Asserts no integer overflow.
    /// Payload is `Bin`.
    div: PayloadNode,
    /// Given a pointer to an array, slice, or pointer, returns a pointer to the element at
    /// the provided index.
    /// AST node is a[b] syntax. Payload is `Bin`.
    elem_ptr_node: PayloadNode,
    /// Same as `elem_ptr_node` but used only for for loop.
    /// AST node is the condition of a for loop.
    /// Payload is `Bin`.
    /// No OOB safety check is emitted.
    elem_ptr: PayloadNode,
    /// Same as `elem_ptr_node` except the index is stored immediately rather than
    /// as a reference to another ZIR instruction.
    /// AST node is an element inside array initialization
    /// syntax. Payload is `ElemPtrImm`.
    /// This instruction has a way to set the result type to be a
    /// single-pointer or a many-pointer.
    elem_ptr_imm: PayloadNode,
    /// Given an array, slice, or pointer, returns the element at the provided index.
    /// AST node is a[b] syntax. Payload is `Bin`.
    elem_val_node: PayloadNode,
    /// Same as `elem_val_node` but used only for for loop.
    /// AST node is the condition of a for loop. Payload is `Bin`.
    /// No OOB safety check is emitted.
    elem_val: PayloadNode,
    /// Emits a compile error if the operand is not `void`.
    ensure_result_used: UnaryNode,
    /// Emits a compile error if an error is ignored.
    ensure_result_non_error: UnaryNode,
    /// Emits a compile error error union payload is not void.
    ensure_err_union_payload_void: UnaryNode,
    /// Create a `E!T` type.
    /// Payload is `Bin`.
    error_union_type: PayloadNode,
    /// `error.Foo` syntax.
    error_value: StringToken,
    /// Implements the `@export` builtin function, based on either an identifier to a Decl,
    /// or field access of a Decl. The thing being exported is the Decl.
    /// Payload is `Export`.
    @"export": PayloadNode,
    /// Implements the `@export` builtin function, based on a comptime-known value.
    /// The thing being exported is the comptime-known value which is the operand.
    /// Payload is `ExportValue`.
    export_value: PayloadNode,
    /// Given a pointer to a struct or object that contains virtual fields, returns a pointer
    /// to the named field. The field name is stored in string_bytes. Used by a.b syntax.
    /// The AST node is the a.b syntax. Payload is Field.
    field_ptr: PayloadNode,
    /// Same as `field_ptr` but used for struct init.
    field_ptr_init: PayloadNode,
    /// Given a struct or object that contains virtual fields, returns the named field.
    /// The field name is stored in string_bytes. Used by a.b syntax.
    /// This instruction also accepts a pointer.
    /// The AST node is the a.b syntax. Payload is Field.
    field_val: PayloadNode,
    /// Given a pointer to a struct or object that contains virtual fields, returns the
    /// named field.  If there is no named field, searches in the type for a decl that
    /// matches the field name.  The decl is resolved and we ensure that it's a function
    /// which can accept the object as the first parameter, with one pointer fixup.  If
    /// all of that works, this instruction produces a special "bound function" value
    /// which contains both the function and the saved first parameter value.
    /// Bound functions may only be used as the function parameter to a `call` or
    /// `builtin_call` instruction.  Any other use is invalid zir and may crash the compiler.
    field_call_bind: PayloadNode,
    /// Given a pointer to a struct or object that contains virtual fields, returns a pointer
    /// to the named field. The field name is a comptime instruction. Used by @field.
    /// The AST node is the builtin call. Payload is FieldNamed.
    field_ptr_named: PayloadNode,
    /// Given a struct or object that contains virtual fields, returns the named field.
    /// The field name is a comptime instruction. Used by @field.
    /// The AST node is the builtin call. Payload is FieldNamed.
    field_val_named: PayloadNode,
    /// Returns a function type, or a function instance, depending on whether
    /// the body_len is 0. Calling convention is auto.
    /// `payload_index` points to a `Func`.
    func: PayloadNode,
    /// Same as `func` but has an inferred error set.
    func_inferred: PayloadNode,
    /// Represents a function declaration or function prototype, depending on
    /// whether body_len is 0.
    /// `payload_index` points to a `FuncFancy`.
    func_fancy: PayloadNode,
    /// Implements the `@import` builtin.
    import: StringToken,
    /// Integer literal that fits in a u64.
    int: u64,
    /// Arbitrary sized integer literal.
    int_big: String,
    /// A float literal that fits in a f64.
    float: f64,
    /// A float literal that fits in a f128.
    /// Payload is `Float128`.
    float128: PayloadNode,
    /// Make an integer type out of signedness and bit count.
    int_type: IntType,
    /// Return a boolean false if an optional is null. `x != null`
    is_non_null: UnaryNode,
    /// Return a boolean false if an optional is null. `x.* != null`
    is_non_null_ptr: UnaryNode,
    /// Return a boolean false if value is an error
    is_non_err: UnaryNode,
    /// Return a boolean false if dereferenced pointer is an error
    is_non_err_ptr: UnaryNode,
    /// Same as `is_non_er` but doesn't validate that the type can be an error.
    ret_is_non_err: UnaryNode,
    /// A labeled block of code that loops forever. At the end of the body will have either
    /// a `repeat` instruction or a `repeat_inline` instruction.
    /// The AST node is either a for loop or while loop.
    /// This ZIR instruction is needed because AIR does not (yet?) match ZIR, and Sema
    /// needs to emit more than 1 AIR block for this instruction.
    /// The payload is `Block`.
    loop: PayloadNode,
    /// Sends runtime control flow back to the beginning of the current block.
    repeat: i32,
    /// Sends comptime control flow back to the beginning of the current block.
    repeat_inline: i32,
    /// Asserts that all the lengths provided match. Used to build a for loop.
    /// Return value is the length as a usize.
    /// Payload is `MultiOp`.
    /// There is exactly one item corresponding to each AST node inside the for
    /// loop condition. Any item may be `none`, indicating an unbounded range.
    /// Illegal behaviors:
    ///  * If all lengths are unbounded ranges (always a compile error).
    ///  * If any two lengths do not match each other.
    for_len: PayloadNode,
    /// Merge two error sets into one, `E1 || E2`.
    /// Payload is `Bin`.
    merge_error_sets: PayloadNode,
    /// Turns an R-Value into a const L-Value. In other words, it takes a value,
    /// stores it in a memory location, and returns a const pointer to it. If the value
    /// is `comptime`, the memory location is global static constant data. Otherwise,
    /// the memory location is in the stack frame, local to the scope containing the
    /// instruction.
    ref: UnaryToken,
    /// Sends control flow back to the function's callee.
    /// Includes an operand as the return value.
    /// Includes an AST node source location.
    ret_node: UnaryNode,
    /// Sends control flow back to the function's callee.
    /// The operand is a `ret_ptr` instruction, where the return value can be found.
    /// Includes an AST node source location.
    ret_load: UnaryNode,
    /// Sends control flow back to the function's callee.
    /// Includes an operand as the return value.
    /// Includes a token source location.
    ret_implicit: UnaryToken,
    /// Sends control flow back to the function's callee.
    /// The return operand is `error.foo` where `foo` is given by the string.
    /// If the current function has an inferred error set, the error given by the
    /// name is added to it.
    ret_err_value: StringToken,
    /// A string name is provided which is an anonymous error set value.
    /// If the current function has an inferred error set, the error given by the
    /// name is added to it.
    /// Results in the error code. Note that control flow is not diverted with
    /// this instruction; a following 'ret' instruction will do the diversion.
    ret_err_value_code: StringToken,
    /// Obtains a pointer to the return value.
    ret_ptr: i32,
    /// Obtains the return type of the in-scope function.
    ret_type: i32,
    /// Create a pointer type which can have a sentinel, alignment, address space, and/or bit range.
    ptr_type: PointerType,
    /// Slice operation `lhs[rhs..]`. No sentinel and no end offset.
    /// Returns a pointer to the subslice.
    /// AST node is the slice syntax. Payload is `SliceStart`.
    slice_start: PayloadNode,
    /// Slice operation `array_ptr[start..end]`. No sentinel.
    /// Returns a pointer to the subslice.
    /// AST node is the slice syntax. Payload is `SliceEnd`.
    slice_end: PayloadNode,
    /// Slice operation `array_ptr[start..end:sentinel]`.
    /// Returns a pointer to the subslice.
    /// AST node is the slice syntax. Payload is `SliceSentinel`.
    slice_sentinel: PayloadNode,
    /// Write a value to a pointer. For loading, see `load`.
    /// Source location is assumed to be same as previous instruction.
    store: Bin,
    /// Same as `store` except provides a source location.
    /// Payload is `Bin`.
    store_node: PayloadNode,
    /// This instruction is not really supposed to be emitted from AstGen; nevertheless it
    /// is sometimes emitted due to deficiencies in AstGen. When Sema sees this instruction,
    /// it must clean up after AstGen's mess by looking at various context clues and
    /// then treating it as one of the following:
    ///  * no-op
    ///  * store_to_inferred_ptr
    ///  * store
    /// LHS is the pointer to store to.
    store_to_block_ptr: Bin,
    /// Same as `store` but the type of the value being stored will be used to infer
    /// the pointer type.
    /// Astgen.zig depends on the ability to change
    /// the tag of an instruction from `store_to_block_ptr` to `store_to_inferred_ptr`
    /// without changing the data.
    store_to_inferred_ptr: Bin,
    /// String Literal. Makes an anonymous Decl and then takes a pointer to it.
    str: String,
    /// Arithmetic negation. Asserts no integer overflow.
    /// Same as sub with a lhs of 0, split into a separate instruction to save memory.
    negate: UnaryNode,
    /// Twos complement wrapping integer negation.
    /// Same as subwrap with a lhs of 0, split into a separate instruction to save memory.
    negate_wrap: UnaryNode,
    /// Returns the type of a value.
    typeof: UnaryNode,
    /// Implements `@TypeOf` for one operand.
    typeof_builtin: PayloadNode,
    /// Given a value, look at the type of it, which must be an integer type.
    /// Returns the integer type for the RHS of a shift operation.
    typeof_log2_int_type: UnaryNode,
    /// Asserts control-flow will not reach this instruction (`unreachable`).
    @"unreachable": Unreachable,
    /// Bitwise XOR. `^`
    /// Payload is `Bin`.
    xor: PayloadNode,
    /// Create an optional type '?T'
    optional_type: UnaryNode,
    /// ?T => T with safety.
    /// Given an optional value, returns the payload value, with a safety check that
    /// the value is non-null. Used for `orelse`, `if` and `while`.
    optional_payload_safe: UnaryNode,
    /// ?T => T without safety.
    /// Given an optional value, returns the payload value. No safety checks.
    optional_payload_unsafe: UnaryNode,
    /// *?T => *T with safety.
    /// Given a pointer to an optional value, returns a pointer to the payload value,
    /// with a safety check that the value is non-null. Used for `orelse`, `if` and `while`.
    optional_payload_safe_ptr: UnaryNode,
    /// *?T => *T without safety.
    /// Given a pointer to an optional value, returns a pointer to the payload value.
    /// No safety checks.
    optional_payload_unsafe_ptr: UnaryNode,
    /// E!T => T without safety.
    /// Given an error union value, returns the payload value. No safety checks.
    err_union_payload_unsafe: UnaryNode,
    /// *E!T => *T without safety.
    /// Given a pointer to a error union value, returns a pointer to the payload value.
    /// No safety checks.
    err_union_payload_unsafe_ptr: UnaryNode,
    /// E!T => E without safety.
    /// Given an error union value, returns the error code. No safety checks.
    err_union_code: UnaryNode,
    /// *E!T => E without safety.
    /// Given a pointer to an error union value, returns the error code. No safety checks.
    err_union_code_ptr: UnaryNode,
    /// An enum literal.
    enum_literal: StringToken,
    /// A switch expression.
    /// AST node is the switch, payload is `SwitchBlock`.
    switch_block: PayloadNode,
    /// Produces the value that will be switched on. For example, for
    /// integers, it returns the integer with no modifications. For tagged unions, it
    /// returns the active enum tag.
    switch_cond: UnaryNode,
    /// Same as `switch_cond`, except the input operand is a pointer to
    /// what will be switched on.
    switch_cond_ref: UnaryNode,
    /// Produces the capture value for a switch prong.
    /// If the `prong_index` field is max int, it means this is the capture
    /// for the else/`_` prong.
    switch_capture: SwitchCapture,
    /// Produces the capture value for a switch prong.
    /// Result is a pointer to the value.
    /// If the `prong_index` field is max int, it means this is the capture
    /// for the else/`_` prong.
    switch_capture_ref: SwitchCapture,
    /// Produces the capture value for a switch prong.
    /// The prong is one of the multi cases.
    switch_capture_multi: SwitchCapture,
    /// Produces the capture value for a switch prong.
    /// The prong is one of the multi cases.
    /// Result is a pointer to the value.
    switch_capture_multi_ref: SwitchCapture,
    /// Produces the capture value for an inline switch prong tag capture.
    switch_capture_tag: UnaryToken,
    /// Given a
    ///   *A returns *A
    ///   *E!A returns *A
    ///   *?A returns *A
    array_base_ptr: UnaryNode,
    /// Given a
    ///   *S returns *S
    ///   *E!S returns *S
    ///   *?S returns *S
    field_base_ptr: UnaryNode,
    /// Checks that the type supports array init syntax.
    validate_array_init_ty: PayloadNode,
    /// Checks that the type supports struct init syntax.
    validate_struct_init_ty: UnaryNode,
    /// Given a set of `field_ptr` instructions, assumes they are all part of a struct
    /// initialization expression, and emits compile errors for duplicate fields
    /// as well as missing fields, if applicable.
    /// This instruction asserts that there is at least one field_ptr instruction,
    /// because it must use one of them to find out the struct type.
    /// Payload is `Block`.
    validate_struct_init: PayloadNode,
    /// Given a set of `elem_ptr_imm` instructions, assumes they are all part of an
    /// array initialization expression, and emits a compile error if the number of
    /// elements does not match the array type.
    /// This instruction asserts that there is at least one `elem_ptr_imm` instruction,
    /// because it must use one of them to find out the array type.
    /// Payload is `Block`.
    validate_array_init: PayloadNode,
    /// Check that operand type supports the dereference operand (.*).
    validate_deref: UnaryNode,
    /// A struct literal with a specified type, with no fields.
    struct_init_empty: UnaryNode,
    /// Given a struct or union, and a field name as a string index,
    /// returns the field type. Payload is `FieldType`.
    field_type: PayloadNode,
    /// Given a struct or union, and a field name as a Ref,
    /// returns the field type. Payload is `FieldTypeRef`.
    field_type_ref: PayloadNode,
    /// Finalizes a typed struct or union initialization, performs validation, and returns the
    /// struct or union value. Payload is `StructInit`.
    struct_init: PayloadNode,
    /// Struct initialization syntax, make the result a pointer.
    /// Payload is `StructInit`.
    struct_init_ref: PayloadNode,
    /// Struct initialization without a type.
    /// Payload is `StructInitAnon`.
    struct_init_anon: PayloadNode,
    /// Anonymous struct initialization syntax, make the result a pointer.
    /// Payload is `StructInitAnon`.
    struct_init_anon_ref: PayloadNode,
    /// Array initialization syntax.
    /// Payload is `MultiOp`.
    array_init: PayloadNode,
    /// Anonymous array initialization syntax.
    /// Payload is `MultiOp`.
    array_init_anon: PayloadNode,
    /// Array initialization syntax, make the result a pointer.
    /// Payload is `MultiOp`.
    array_init_ref: PayloadNode,
    /// Anonymous array initialization syntax, make the result a pointer.
    /// Payload is `MultiOp`.
    array_init_anon_ref: PayloadNode,
    /// Implements the `@unionInit` builtin.
    /// Payload is `UnionInit`.
    union_init: PayloadNode,
    /// Implements the `@typeInfo` builtin.
    type_info: UnaryNode,
    /// Implements the `@sizeOf` builtin.
    size_of: UnaryNode,
    /// Implements the `@bitSizeOf` builtin.
    bit_size_of: UnaryNode,

    /// Implement builtin `@ptrToInt`.
    /// Convert a pointer to a `usize` integer.
    ptr_to_int: UnaryNode,
    /// Emit an error message and fail compilation.
    compile_error: UnaryNode,
    /// Changes the maximum number of backwards branches that compile-time
    /// code execution can use before giving up and making a compile error.
    set_eval_branch_quota: UnaryNode,
    /// Converts an enum value into an integer. Resulting type will be the tag type
    enum_to_int: UnaryNode,
    /// Implement builtin `@alignOf`.
    align_of: UnaryNode,
    /// Implement builtin `@boolToInt`.
    bool_to_int: UnaryNode,
    /// Implement builtin `@embedFile`.
    embed_file: UnaryNode,
    /// Implement builtin `@errorName`.
    error_name: UnaryNode,
    /// Implement builtin `@panic`.
    panic: UnaryNode,
    /// Implements `@trap`.
    trap: i32,
    /// Implement builtin `@setRuntimeSafety`.
    set_runtime_safety: UnaryNode,
    /// Implement builtin `@sqrt`.
    sqrt: UnaryNode,
    /// Implement builtin `@sin`.
    sin: UnaryNode,
    /// Implement builtin `@cos`.
    cos: UnaryNode,
    /// Implement builtin `@tan`.
    tan: UnaryNode,
    /// Implement builtin `@exp`.
    exp: UnaryNode,
    /// Implement builtin `@exp2`.
    exp2: UnaryNode,
    /// Implement builtin `@log`.
    log: UnaryNode,
    /// Implement builtin `@log2`.
    log2: UnaryNode,
    /// Implement builtin `@log10`.
    log10: UnaryNode,
    /// Implement builtin `@fabs`.
    fabs: UnaryNode,
    /// Implement builtin `@floor`.
    floor: UnaryNode,
    /// Implement builtin `@ceil`.
    ceil: UnaryNode,
    /// Implement builtin `@trunc`.
    trunc: UnaryNode,
    /// Implement builtin `@round`.
    round: UnaryNode,
    /// Implement builtin `@tagName`.
    tag_name: UnaryNode,
    /// Implement builtin `@typeName`.
    type_name: UnaryNode,
    /// Implement builtin `@Frame`.
    frame_type: UnaryNode,
    /// Implement builtin `@frameSize`.
    frame_size: UnaryNode,

    /// Implements the `@floatToInt` builtin.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    float_to_int: PayloadNode,
    /// Implements the `@intToFloat` builtin.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    int_to_float: PayloadNode,
    /// Implements the `@intToPtr` builtin.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    int_to_ptr: PayloadNode,
    /// Converts an integer into an enum value.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    int_to_enum: PayloadNode,
    /// Convert a larger float type to any other float type, possibly causing
    /// a loss of precision. AST is the `@floatCast` syntax.
    /// Payload is `Bin` with lhs as the dest type, rhs the operand.
    float_cast: PayloadNode,
    /// Implements the `@intCast` builtin.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    /// Convert an integer value to another integer type, asserting that the destination type
    /// can hold the same mathematical value.
    int_cast: PayloadNode,
    /// Implements the `@ptrCast` builtin.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    ptr_cast: PayloadNode,
    /// Implements the `@truncate` builtin.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    truncate: PayloadNode,
    /// Implements the `@alignCast` builtin.
    /// Payload is `Bin`. `lhs` is dest type, `rhs` is operand.
    align_cast: PayloadNode,

    /// Implements the `@hasDecl` builtin. Payload is `Bin`.
    has_decl: PayloadNode,
    /// Implements the `@hasField` builtin. Payload is `Bin`.
    has_field: PayloadNode,

    /// Implements the `@clz` builtin.
    clz: UnaryNode,
    /// Implements the `@ctz` builtin.
    ctz: UnaryNode,
    /// Implements the `@popCount` builtin.
    pop_count: UnaryNode,
    /// Implements the `@byteSwap` builtin.
    byte_swap: UnaryNode,
    /// Implements the `@bitReverse` builtin.
    bit_reverse: UnaryNode,

    /// Implements the `@bitOffsetOf` builtin.
    /// Payload is `Bin`.
    bit_offset_of: PayloadNode,
    /// Implements the `@offsetOf` builtin.
    /// Payload is `Bin`.
    offset_of: PayloadNode,
    /// Implements the `@splat` builtin.
    /// Payload is `Bin`.
    splat: PayloadNode,
    /// Implements the `@reduce` builtin.
    /// Payload is `Bin`.
    reduce: PayloadNode,
    /// Implements the `@shuffle` builtin.
    /// Payload is `Shuffle`.
    shuffle: PayloadNode,
    /// Implements the `@atomicLoad` builtin.
    /// UsesPayload is `AtomicLoad`.
    atomic_load: PayloadNode,
    /// Implements the `@atomicRmw` builtin.
    /// Payload is `AtomicRmw`.
    atomic_rmw: PayloadNode,
    /// Implements the `@atomicStore` builtin.
    /// Payload is `AtomicStore`.
    atomic_store: PayloadNode,
    /// Implements the `@mulAdd` builtin.
    /// Payload is `MulAdd`.
    /// The addend communicates the type of the builtin.
    /// The mulends need to be coerced to the same type.
    mul_add: PayloadNode,
    /// Implements the `@fieldParentPtr` builtin.
    /// Payload is `FieldParentPtr`.
    field_parent_ptr: PayloadNode,
    /// Implements the `@memcpy` builtin.
    /// Payload is `Bin`.
    memcpy: PayloadNode,
    /// Implements the `@memset` builtin.
    /// Payload is `Bin`.
    memset: PayloadNode,
    /// Implements the `@min` builtin.
    /// Payload is `Bin`
    min: PayloadNode,
    /// Implements the `@max` builtin.
    /// Payload is `Bin`
    max: PayloadNode,
    /// Implements the `@cImport` builtin.
    /// Payload is `Block`.
    c_import: PayloadNode,

    /// Allocates stack local memory.
    /// The operand is the type of the allocated object.
    /// The node source location points to a var decl node.
    alloc: UnaryNode,
    /// Same as `alloc` except mutable.
    alloc_mut: UnaryNode,
    /// Allocates comptime-mutable memory.
    /// The operand is the type of the allocated object.
    /// The node source location points to a var decl node.
    alloc_comptime_mut: UnaryNode,
    /// Same as `alloc` except the type is inferred.
    alloc_inferred: i32,
    /// Same as `alloc_inferred` except mutable.
    alloc_inferred_mut: i32,
    /// Allocates comptime const memory.
    /// The type of the allocated object is inferred.
    /// The node source location points to a var decl node.
    alloc_inferred_comptime: i32,
    /// Same as `alloc_comptime_mut` except the type is inferred.
    alloc_inferred_comptime_mut: i32,
    /// Each `store_to_inferred_ptr` puts the type of the stored value into a set: aeiou,
    /// and then `resolve_inferred_alloc` triggers peer type resolution on the set.
    /// The operand is a `alloc_inferred` or `alloc_inferred_mut` instruction, which
    /// is the allocation that needs to have its type inferred.
    /// The AST node is the var decl.
    resolve_inferred_alloc: UnaryNode,
    /// Turns a pointer coming from an `alloc`, `alloc_inferred`, `alloc_inferred_comptime` or
    /// `Extended.alloc` into a constant version of the same pointer.
    make_ptr_const: UnaryNode,

    /// Implements `resume` syntax.
    @"resume": UnaryNode,
    @"await": UnaryNode,

    /// When a type or function refers to a comptime value from an outer
    /// scope, that forms a closure over comptime value.  The outer scope
    /// will record a capture of that value, which encodes its current state
    /// and marks it to persist. Operand is the instruction value to capture.
    closure_capture: UnaryToken,
    /// The inner scope of a closure uses closure_get to retrieve the value
    /// stored by the outer scope. Operand is the closure_capture instruction ref.
    closure_get: InstNode,

    /// A defer statement.
    @"defer": struct {
        index: u32,
        len: u32,
    },
    /// An errdefer statement with a code.
    defer_err_code: struct {
        err_code: Ref,
        payload_index: u32,
    },

    /// Requests that Sema update the saved error return trace index for the enclosing
    /// block, if the operand is .none or of an error/error-union type.
    save_err_ret_index: Ref, // If error type (or .none), save new trace index
    /// Sets error return trace to zero if no operand is given: aeiou,
    /// otherwise sets the value to the given amount.
    restore_err_ret_index: struct {
        block: Ref, // If restored, the index is from this block's entrypoint
        operand: Ref, // If non-error (or .none), then restore the index
    },

    /// The ZIR instruction tag is one of the `Extended` ones.
    /// Uses the `extended` union field.
    extended: Extended.InstData,

    pub const PayloadNode = struct {
        /// Offset from Decl AST node index.
        /// `Tag` determines which kind of AST node this points to.
        src_node: i32,
        /// index into extra.
        /// `Tag` determines what lives there.
        payload_index: u32,

        pub fn src(self: @This()) LazySrcLoc {
            return LazySrcLoc.nodeOffset(self.src_node);
        }
    };
    pub const UnaryNode = struct {
        /// Offset from Decl AST node index.
        src_node: i32,
        /// The meaning of this operand depends on the corresponding `Tag`.
        operand: Ref,

        pub fn src(self: @This()) LazySrcLoc {
            return LazySrcLoc.nodeOffset(self.src_node);
        }
    };
    /// Used for unary operators which reference an inst,
    /// with an AST node source location.
    pub const InstNode = struct {
        /// Offset from Decl AST node index.
        src_node: i32,
        /// The meaning of this operand depends on the corresponding `Tag`.
        inst: Index,

        pub fn src(self: @This()) LazySrcLoc {
            return LazySrcLoc.nodeOffset(self.src_node);
        }
    };
    pub const PayloadToken = struct {
        /// Offset from Decl AST token index.
        src_tok: Ast.TokenIndex,
        /// index into extra.
        /// `Tag` determines what lives there.
        payload_index: u32,

        pub fn src(self: @This()) LazySrcLoc {
            return .{ .token_offset = self.src_tok };
        }
    };
    pub const UnaryToken = struct {
        /// Offset from Decl AST token index.
        src_tok: Ast.TokenIndex,
        /// The meaning of this operand depends on the corresponding `Tag`.
        operand: Ref,

        pub fn src(self: @This()) LazySrcLoc {
            return .{ .token_offset = self.src_tok };
        }
    };
    pub const StringToken = struct {
        /// Offset into `string_bytes`. Null-terminated.
        start: u32,
        /// Offset from Decl AST token index.
        src_tok: u32,

        pub fn get(self: @This(), code: Zir) [:0]const u8 {
            return code.nullTerminatedString(self.start);
        }

        pub fn src(self: @This()) LazySrcLoc {
            return .{ .token_offset = self.src_tok };
        }
    };
    pub const StringOperator = struct {
        /// Offset into `string_bytes`. Null-terminated.
        str: u32,
        operand: Ref,

        pub fn getStr(self: @This(), zir: Zir) [:0]const u8 {
            return zir.nullTerminatedString(self.str);
        }
    };
    pub const BoolBreak = struct {
        lhs: Ref,
        /// Points to a `Block`.
        payload_index: u32,
    };
    pub const SwitchCapture = struct {
        switch_inst: Index,
        prong_index: u32,
    };
    pub const BreakNode = struct {
        operand: Ref,
        payload_index: u32,
    };
    pub const String = struct {
        /// Offset into `string_bytes`.
        start: u32,
        /// Number of bytes in the string.
        len: u32,

        pub fn get(self: @This(), code: Zir) []const u8 {
            return code.string_bytes[self.start..][0..self.len];
        }
    };
    pub const IntType = struct {
        /// Offset from Decl AST node index.
        /// `Tag` determines which kind of AST node this points to.
        src_node: i32,
        signedness: std.builtin.Signedness,
        bit_count: u16,

        pub fn src(self: @This()) LazySrcLoc {
            return LazySrcLoc.nodeOffset(self.src_node);
        }
    };
    pub const PointerType = struct {
        flags: packed struct {
            is_allowzero: bool,
            is_mutable: bool,
            is_volatile: bool,
            has_sentinel: bool,
            has_align: bool,
            has_addrspace: bool,
            has_bit_range: bool,
            _: u1 = undefined,
        },
        size: std.builtin.Type.Pointer.Size,
        /// Index into extra. See `PtrType`.
        payload_index: u32,
    };
    pub const Unreachable = struct {
        /// Offset from Decl AST node index.
        /// `Tag` determines which kind of AST node this points to.
        src_node: i32,

        pub fn src(self: @This()) LazySrcLoc {
            return LazySrcLoc.nodeOffset(self.src_node);
        }
    };

    /// Rarer instructions are here; ones that do not fit in the 8-bit `Tag` enum.
    /// `noreturn` instructions may not go here; they must be part of the main `Tag` enum.
    pub const Extended = enum(u16) {
        /// Declares a global variable.
        /// `operand` is payload index to `ExtendedVar`.
        /// `small` is `ExtendedVar.Small`.
        variable,
        /// A struct type definition. Contains references to ZIR instructions for
        /// the field types, defaults, and alignments.
        /// `operand` is payload index to `StructDecl`.
        /// `small` is `StructDecl.Small`.
        struct_decl,
        /// An enum type definition. Contains references to ZIR instructions for
        /// the field value expressions and optional type tag expression.
        /// `operand` is payload index to `EnumDecl`.
        /// `small` is `EnumDecl.Small`.
        enum_decl,
        /// A union type definition. Contains references to ZIR instructions for
        /// the field types and optional type tag expression.
        /// `operand` is payload index to `UnionDecl`.
        /// `small` is `UnionDecl.Small`.
        union_decl,
        /// An opaque type definition. Contains references to decls and captures.
        /// `operand` is payload index to `OpaqueDecl`.
        /// `small` is `OpaqueDecl.Small`.
        opaque_decl,
        /// Implements the `@This` builtin.
        /// `operand` is `src_node: i32`.
        this,
        /// Implements the `@returnAddress` builtin.
        /// `operand` is `src_node: i32`.
        ret_addr,
        /// Implements the `@src` builtin.
        /// `operand` is payload index to `LineColumn`.
        builtin_src,
        /// Implements the `@errorReturnTrace` builtin.
        /// `operand` is `src_node: i32`.
        error_return_trace,
        /// Implements the `@frame` builtin.
        /// `operand` is `src_node: i32`.
        frame,
        /// Implements the `@frameAddress` builtin.
        /// `operand` is `src_node: i32`.
        frame_address,
        /// Same as `alloc` from `Tag` but may contain an alignment instruction.
        /// `operand` is payload index to `AllocExtended`.
        /// `small`:
        ///  * 0b000X - has type
        ///  * 0b00X0 - has alignment
        ///  * 0b0X00 - 1=const, 0=var
        ///  * 0bX000 - is comptime
        alloc,
        /// The `@extern` builtin.
        /// `operand` is payload index to `BinNode`.
        builtin_extern,
        /// Inline assembly.
        /// `small`:
        ///  * 0b00000000_000XXXXX - `outputs_len`.
        ///  * 0b000000XX_XXX00000 - `inputs_len`.
        ///  * 0b0XXXXX00_00000000 - `clobbers_len`.
        ///  * 0bX0000000_00000000 - is volatile
        /// `operand` is payload index to `Asm`.
        @"asm",
        /// Same as `asm` except the assembly template is not a string literal but a comptime
        /// expression.
        /// The `asm_source` field of the Asm is not a null-terminated string
        /// but instead a Ref.
        asm_expr,
        /// Log compile time variables and emit an error message.
        /// `operand` is payload index to `NodeMultiOp`.
        /// `small` is `operands_len`.
        /// The AST node is the compile log builtin call.
        compile_log,
        /// The builtin `@TypeOf` which returns the type after Peer Type Resolution
        /// of one or more params.
        /// `operand` is payload index to `NodeMultiOp`.
        /// `small` is `operands_len`.
        /// The AST node is the builtin call.
        typeof_peer,
        /// Implements the `@addWithOverflow` builtin.
        /// `operand` is payload index to `BinNode`.
        /// `small` is unused.
        add_with_overflow,
        /// Implements the `@subWithOverflow` builtin.
        /// `operand` is payload index to `BinNode`.
        /// `small` is unused.
        sub_with_overflow,
        /// Implements the `@mulWithOverflow` builtin.
        /// `operand` is payload index to `BinNode`.
        /// `small` is unused.
        mul_with_overflow,
        /// Implements the `@shlWithOverflow` builtin.
        /// `operand` is payload index to `BinNode`.
        /// `small` is unused.
        shl_with_overflow,
        /// `operand` is payload index to `UnNode`.
        c_undef,
        /// `operand` is payload index to `UnNode`.
        c_include,
        /// `operand` is payload index to `BinNode`.
        c_define,
        /// `operand` is payload index to `UnNode`.
        wasm_memory_size,
        /// `operand` is payload index to `BinNode`.
        wasm_memory_grow,
        /// The `@prefetch` builtin.
        /// `operand` is payload index to `BinNode`.
        prefetch,
        /// Given a pointer to a struct or object that contains virtual fields, returns the
        /// named field.  If there is no named field, searches in the type for a decl that
        /// matches the field name.  The decl is resolved and we ensure that it's a function
        /// which can accept the object as the first parameter, with one pointer fixup.  If
        /// all of that works, this instruction produces a special "bound function" value
        /// which contains both the function and the saved first parameter value.
        /// Bound functions may only be used as the function parameter to a `call` or
        /// `builtin_call` instruction.  Any other use is invalid zir and may crash the compiler.
        /// Uses `pl_node` field. The AST node is the `@field` builtin. Payload is FieldNamedNode.
        field_call_bind_named,
        /// Implements the `@fence` builtin.
        /// `operand` is payload index to `UnNode`.
        fence,
        /// Implement builtin `@setFloatMode`.
        /// `operand` is payload index to `UnNode`.
        set_float_mode,
        /// Implement builtin `@setAlignStack`.
        /// `operand` is payload index to `UnNode`.
        set_align_stack,
        /// Implements `@setCold`.
        /// `operand` is payload index to `UnNode`.
        set_cold,
        /// Implements the `@errSetCast` builtin.
        /// `operand` is payload index to `BinNode`. `lhs` is dest type, `rhs` is operand.
        err_set_cast,
        /// `operand` is payload index to `UnNode`.
        await_nosuspend,
        /// Implements `@breakpoint`.
        /// `operand` is `src_node: i32`.
        breakpoint,
        /// Implements the `@select` builtin.
        /// operand` is payload index to `Select`.
        select,
        /// Implement builtin `@errToInt`.
        /// `operand` is payload index to `UnNode`.
        error_to_int,
        /// Implement builtin `@intToError`.
        /// `operand` is payload index to `UnNode`.
        int_to_error,
        /// Implement builtin `@Type`.
        /// `operand` is payload index to `UnNode`.
        /// `small` contains `NameStrategy`.
        reify,
        /// Implements the `@asyncCall` builtin.
        /// `operand` is payload index to `AsyncCall`.
        builtin_async_call,
        /// Implements the `@cmpxchgStrong` and `@cmpxchgWeak` builtins.
        /// `small` 0=>weak 1=>strong
        /// `operand` is payload index to `Cmpxchg`.
        cmpxchg,
        /// Implement the builtin `@addrSpaceCast`
        /// `Operand` is payload index to `BinNode`. `lhs` is dest type, `rhs` is operand.
        addrspace_cast,
        /// Implement builtin `@cVaArg`.
        /// `operand` is payload index to `BinNode`.
        c_va_arg,
        /// Implement builtin `@cVaCopy`.
        /// `operand` is payload index to `UnNode`.
        c_va_copy,
        /// Implement builtin `@cVaEnd`.
        /// `operand` is payload index to `UnNode`.
        c_va_end,
        /// Implement builtin `@cVaStart`.
        /// `operand` is `src_node: i32`.
        c_va_start,
        /// Implements the `@constCast` builtin.
        /// `operand` is payload index to `UnNode`.
        const_cast,
        /// Implements the `@volatileCast` builtin.
        /// `operand` is payload index to `UnNode`.
        volatile_cast,
        /// Implements the `@workItemId` builtin.
        /// `operand` is payload index to `UnNode`.
        work_item_id,
        /// Implements the `@workGroupSize` builtin.
        /// `operand` is payload index to `UnNode`.
        work_group_size,
        /// Implements the `@workGroupId` builtin.
        /// `operand` is payload index to `UnNode`.
        work_group_id,
        /// Implements the `@inComptime` builtin.
        /// `operand` is `src_node: i32`.
        in_comptime,

        pub const InstData = struct {
            opcode: Extended,
            small: u16,
            operand: u32,
        };
    };

    /// The position of a ZIR instruction within the `Zir` instructions array.
    pub const Index = u32;

    /// A reference to a TypedValue or ZIR instruction.
    ///
    /// If the Ref has a tag in this enum, it refers to a TypedValue.
    ///
    /// If the value of a Ref does not have a tag, it refers to a ZIR instruction.
    ///
    /// The first values after the the last tag refer to ZIR instructions which may
    /// be derived by subtracting `typed_value_map.len`.
    ///
    /// When adding a tag to this enum, consider adding a corresponding entry to
    /// `primitives` in astgen.
    ///
    /// The tag type is specified so that it is safe to bitcast between `[]u32`
    /// and `[]Ref`.
    pub const Ref = enum(u32) {
        /// This Ref does not correspond to any ZIR instruction or constant
        /// value and may instead be used as a sentinel to indicate null.
        none,

        u1_type,
        u8_type,
        i8_type,
        u16_type,
        i16_type,
        u29_type,
        u32_type,
        i32_type,
        u64_type,
        i64_type,
        u128_type,
        i128_type,
        usize_type,
        isize_type,
        c_char_type,
        c_short_type,
        c_ushort_type,
        c_int_type,
        c_uint_type,
        c_long_type,
        c_ulong_type,
        c_longlong_type,
        c_ulonglong_type,
        c_longdouble_type,
        f16_type,
        f32_type,
        f64_type,
        f80_type,
        f128_type,
        anyopaque_type,
        bool_type,
        void_type,
        type_type,
        anyerror_type,
        comptime_int_type,
        comptime_float_type,
        noreturn_type,
        anyframe_type,
        null_type,
        undefined_type,
        enum_literal_type,
        atomic_order_type,
        atomic_rmw_op_type,
        calling_convention_type,
        address_space_type,
        float_mode_type,
        reduce_op_type,
        modifier_type,
        prefetch_options_type,
        export_options_type,
        extern_options_type,
        type_info_type,
        manyptr_u8_type,
        manyptr_const_u8_type,
        fn_noreturn_no_args_type,
        fn_void_no_args_type,
        fn_naked_noreturn_no_args_type,
        fn_ccc_void_no_args_type,
        single_const_pointer_to_comptime_int_type,
        const_slice_u8_type,
        anyerror_void_error_union_type,
        generic_poison_type,

        /// `undefined` (untyped)
        undef,
        /// `0` (comptime_int)
        zero,
        /// `1` (comptime_int)
        one,
        /// `{}`
        void_value,
        /// `unreachable` (noreturn type)
        unreachable_value,
        /// `null` (untyped)
        null_value,
        /// `true`
        bool_true,
        /// `false`
        bool_false,
        /// `.{}` (untyped)
        empty_struct,
        /// `0` (usize)
        zero_usize,
        /// `1` (usize)
        one_usize,
        /// `std.builtin.CallingConvention.C`
        calling_convention_c,
        /// `std.builtin.CallingConvention.Inline`
        calling_convention_inline,
        /// Used for generic parameters where the type and value
        /// is not known until generic function instantiation.
        generic_poison,

        _,

        pub const typed_value_map = std.enums.directEnumArray(Ref, TypedValue, 0, .{
            .none = undefined,

            .u1_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.u1_type),
            },
            .u8_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.u8_type),
            },
            .i8_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.i8_type),
            },
            .u16_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.u16_type),
            },
            .i16_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.i16_type),
            },
            .u29_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.u29_type),
            },
            .u32_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.u32_type),
            },
            .i32_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.i32_type),
            },
            .u64_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.u64_type),
            },
            .i64_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.i64_type),
            },
            .u128_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.u128_type),
            },
            .i128_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.i128_type),
            },
            .usize_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.usize_type),
            },
            .isize_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.isize_type),
            },
            .c_char_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_char_type),
            },
            .c_short_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_short_type),
            },
            .c_ushort_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_ushort_type),
            },
            .c_int_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_int_type),
            },
            .c_uint_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_uint_type),
            },
            .c_long_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_long_type),
            },
            .c_ulong_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_ulong_type),
            },
            .c_longlong_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_longlong_type),
            },
            .c_ulonglong_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_ulonglong_type),
            },
            .c_longdouble_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.c_longdouble_type),
            },
            .f16_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.f16_type),
            },
            .f32_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.f32_type),
            },
            .f64_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.f64_type),
            },
            .f80_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.f80_type),
            },
            .f128_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.f128_type),
            },
            .anyopaque_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.anyopaque_type),
            },
            .bool_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.bool_type),
            },
            .void_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.void_type),
            },
            .type_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.type_type),
            },
            .anyerror_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.anyerror_type),
            },
            .comptime_int_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.comptime_int_type),
            },
            .comptime_float_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.comptime_float_type),
            },
            .noreturn_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.noreturn_type),
            },
            .anyframe_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.anyframe_type),
            },
            .null_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.null_type),
            },
            .undefined_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.undefined_type),
            },
            .fn_noreturn_no_args_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.fn_noreturn_no_args_type),
            },
            .fn_void_no_args_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.fn_void_no_args_type),
            },
            .fn_naked_noreturn_no_args_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.fn_naked_noreturn_no_args_type),
            },
            .fn_ccc_void_no_args_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.fn_ccc_void_no_args_type),
            },
            .single_const_pointer_to_comptime_int_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.single_const_pointer_to_comptime_int_type),
            },
            .const_slice_u8_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.const_slice_u8_type),
            },
            .anyerror_void_error_union_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.anyerror_void_error_union_type),
            },
            .generic_poison_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.generic_poison_type),
            },
            .enum_literal_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.enum_literal_type),
            },
            .manyptr_u8_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.manyptr_u8_type),
            },
            .manyptr_const_u8_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.manyptr_const_u8_type),
            },
            .atomic_order_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.atomic_order_type),
            },
            .atomic_rmw_op_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.atomic_rmw_op_type),
            },
            .calling_convention_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.calling_convention_type),
            },
            .address_space_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.address_space_type),
            },
            .float_mode_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.float_mode_type),
            },
            .reduce_op_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.reduce_op_type),
            },
            .modifier_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.modifier_type),
            },
            .prefetch_options_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.prefetch_options_type),
            },
            .export_options_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.export_options_type),
            },
            .extern_options_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.extern_options_type),
            },
            .type_info_type = .{
                .ty = Type.initTag(.type),
                .val = Value.initTag(.type_info_type),
            },

            .undef = .{
                .ty = Type.initTag(.undefined),
                .val = Value.initTag(.undef),
            },
            .zero = .{
                .ty = Type.initTag(.comptime_int),
                .val = Value.initTag(.zero),
            },
            .zero_usize = .{
                .ty = Type.initTag(.usize),
                .val = Value.initTag(.zero),
            },
            .one = .{
                .ty = Type.initTag(.comptime_int),
                .val = Value.initTag(.one),
            },
            .one_usize = .{
                .ty = Type.initTag(.usize),
                .val = Value.initTag(.one),
            },
            .void_value = .{
                .ty = Type.initTag(.void),
                .val = Value.initTag(.void_value),
            },
            .unreachable_value = .{
                .ty = Type.initTag(.noreturn),
                .val = Value.initTag(.unreachable_value),
            },
            .null_value = .{
                .ty = Type.initTag(.null),
                .val = Value.initTag(.null_value),
            },
            .bool_true = .{
                .ty = Type.initTag(.bool),
                .val = Value.initTag(.bool_true),
            },
            .bool_false = .{
                .ty = Type.initTag(.bool),
                .val = Value.initTag(.bool_false),
            },
            .empty_struct = .{
                .ty = Type.initTag(.empty_struct_literal),
                .val = Value.initTag(.empty_struct_value),
            },
            .calling_convention_c = .{
                .ty = Type.initTag(.calling_convention),
                .val = .{ .ptr_otherwise = &calling_convention_c_payload.base },
            },
            .calling_convention_inline = .{
                .ty = Type.initTag(.calling_convention),
                .val = .{ .ptr_otherwise = &calling_convention_inline_payload.base },
            },
            .generic_poison = .{
                .ty = Type.initTag(.generic_poison),
                .val = Value.initTag(.generic_poison),
            },
        });
    };

    /// We would like this to be const but `Value` wants a mutable pointer for
    /// its payload field. Nothing should mutate this though.
    var calling_convention_c_payload: Value.Payload.U32 = .{
        .base = .{ .tag = .enum_field_index },
        .data = @enumToInt(std.builtin.CallingConvention.C),
    };

    /// We would like this to be const but `Value` wants a mutable pointer for
    /// its payload field. Nothing should mutate this though.
    var calling_convention_inline_payload: Value.Payload.U32 = .{
        .base = .{ .tag = .enum_field_index },
        .data = @enumToInt(std.builtin.CallingConvention.Inline),
    };

    pub const Break = struct {
        pub const no_src_node = std.math.maxInt(i32);

        block_inst: Index,
        operand_src_node: i32,
    };

    /// Trailing:
    /// 0. Output for every outputs_len
    /// 1. Input for every inputs_len
    /// 2. clobber: u32 // index into string_bytes (null terminated) for every clobbers_len.
    pub const Asm = struct {
        src_node: i32,
        // null-terminated string index
        asm_source: u32,
        /// 1 bit for each outputs_len: whether it uses `-> T` or not.
        ///   0b0 - operand is a pointer to where to store the output.
        ///   0b1 - operand is a type; asm expression has the output as the result.
        /// 0b0X is the first output, 0bX0 is the second, etc.
        output_type_bits: u32,

        pub const Output = struct {
            /// index into string_bytes (null terminated)
            name: u32,
            /// index into string_bytes (null terminated)
            constraint: u32,
            /// How to interpret this is determined by `output_type_bits`.
            operand: Ref,
        };

        pub const Input = struct {
            /// index into string_bytes (null terminated)
            name: u32,
            /// index into string_bytes (null terminated)
            constraint: u32,
            operand: Ref,
        };
    };

    /// Trailing:
    /// if (ret_body_len == 1) {
    ///   0. return_type: Ref
    /// }
    /// if (ret_body_len > 1) {
    ///   1. return_type: Index // for each ret_body_len
    /// }
    /// 2. body: Index // for each body_len
    /// 3. src_locs: SrcLocs // if body_len != 0
    pub const Func = struct {
        /// If this is 0 it means a void return type.
        /// If this is 1 it means return_type is a simple Ref
        ret_body_len: u32,
        /// Points to the block that contains the param instructions for this function.
        param_block: Index,
        body_len: u32,

        pub const SrcLocs = struct {
            /// Line index in the source file relative to the parent decl.
            lbrace_line: u32,
            /// Line index in the source file relative to the parent decl.
            rbrace_line: u32,
            /// lbrace_column is least significant bits u16
            /// rbrace_column is most significant bits u16
            columns: u32,
        };
    };

    /// Trailing:
    /// 0. lib_name: u32, // null terminated string index, if has_lib_name is set
    /// if (has_align_ref and !has_align_body) {
    ///   1. align: Ref,
    /// }
    /// if (has_align_body) {
    ///   2. align_body_len: u32
    ///   3. align_body: u32 // for each align_body_len
    /// }
    /// if (has_addrspace_ref and !has_addrspace_body) {
    ///   4. addrspace: Ref,
    /// }
    /// if (has_addrspace_body) {
    ///   5. addrspace_body_len: u32
    ///   6. addrspace_body: u32 // for each addrspace_body_len
    /// }
    /// if (has_section_ref and !has_section_body) {
    ///   7. section: Ref,
    /// }
    /// if (has_section_body) {
    ///   8. section_body_len: u32
    ///   9. section_body: u32 // for each section_body_len
    /// }
    /// if (has_cc_ref and !has_cc_body) {
    ///   10. cc: Ref,
    /// }
    /// if (has_cc_body) {
    ///   11. cc_body_len: u32
    ///   12. cc_body: u32 // for each cc_body_len
    /// }
    /// if (has_ret_ty_ref and !has_ret_ty_body) {
    ///   13. ret_ty: Ref,
    /// }
    /// if (has_ret_ty_body) {
    ///   14. ret_ty_body_len: u32
    ///   15. ret_ty_body: u32 // for each ret_ty_body_len
    /// }
    /// 16. noalias_bits: u32 // if has_any_noalias
    ///     - each bit starting with LSB corresponds to parameter indexes
    /// 17. body: Index // for each body_len
    /// 18. src_locs: Func.SrcLocs // if body_len != 0
    pub const FuncFancy = struct {
        /// Points to the block that contains the param instructions for this function.
        param_block: Index,
        body_len: u32,
        bits: Bits,

        /// If both has_cc_ref and has_cc_body are false, it means auto calling convention.
        /// If both has_align_ref and has_align_body are false, it means default alignment.
        /// If both has_ret_ty_ref and has_ret_ty_body are false, it means void return type.
        /// If both has_section_ref and has_section_body are false, it means default section.
        /// If both has_addrspace_ref and has_addrspace_body are false, it means default addrspace.
        pub const Bits = packed struct {
            is_var_args: bool,
            is_inferred_error: bool,
            is_test: bool,
            is_extern: bool,
            is_noinline: bool,
            has_align_ref: bool,
            has_align_body: bool,
            has_addrspace_ref: bool,
            has_addrspace_body: bool,
            has_section_ref: bool,
            has_section_body: bool,
            has_cc_ref: bool,
            has_cc_body: bool,
            has_ret_ty_ref: bool,
            has_ret_ty_body: bool,
            has_lib_name: bool,
            has_any_noalias: bool,
            _: u15 = undefined,
        };
    };

    /// Trailing:
    /// 0. lib_name: u32, // null terminated string index, if has_lib_name is set
    /// 1. align: Ref, // if has_align is set
    /// 2. init: Ref // if has_init is set
    /// The source node is obtained from the containing `block_inline`.
    pub const ExtendedVar = struct {
        var_type: Ref,

        pub const Small = packed struct {
            has_lib_name: bool,
            has_align: bool,
            has_init: bool,
            is_extern: bool,
            is_threadlocal: bool,
            _: u11 = undefined,
        };
    };

    /// This data is stored inside extra, with trailing operands according to `operands_len`.
    /// Each operand is a `Ref`.
    pub const MultiOp = struct {
        operands_len: u32,
    };

    /// Trailing: operand: Ref, // for each `operands_len` (stored in `small`).
    pub const NodeMultiOp = struct {
        src_node: i32,
    };

    /// This data is stored inside extra, with trailing operands according to `body_len`.
    /// Each operand is an `Index`.
    pub const Block = struct {
        body_len: u32,
    };

    /// Stored inside extra, with trailing arguments according to `args_len`.
    /// Implicit 0. arg_0_start: u32, // always same as `args_len`
    /// 1. arg_end: u32, // for each `args_len`
    /// arg_N_start is the same as arg_N-1_end
    pub const Call = struct {
        // Note: Flags *must* come first so that unusedResultExpr
        // can find it when it goes to modify them.
        flags: Flags,
        callee: Ref,

        pub const Flags = packed struct {
            /// std.builtin.CallModifier in packed form
            pub const PackedModifier = u3;
            pub const PackedArgsLen = u27;

            packed_modifier: PackedModifier,
            ensure_result_used: bool = false,
            pop_error_return_trace: bool,
            args_len: PackedArgsLen,

            comptime {
                if (@sizeOf(Flags) != 4 or @bitSizeOf(Flags) != 32)
                    @compileError("Layout of Call.Flags needs to be updated!");
                if (@bitSizeOf(std.builtin.CallModifier) != @bitSizeOf(PackedModifier))
                    @compileError("Call.Flags.PackedModifier needs to be updated!");
            }
        };
    };

    pub const TypeOfPeer = struct {
        src_node: i32,
        body_len: u32,
        body_index: u32,
    };

    pub const BuiltinCall = struct {
        // Note: Flags *must* come first so that unusedResultExpr
        // can find it when it goes to modify them.
        flags: Flags,
        modifier: Ref,
        callee: Ref,
        args: Ref,

        pub const Flags = packed struct {
            is_nosuspend: bool,
            ensure_result_used: bool,
            _: u30 = undefined,

            comptime {
                if (@sizeOf(Flags) != 4 or @bitSizeOf(Flags) != 32)
                    @compileError("Layout of BuiltinCall.Flags needs to be updated!");
            }
        };
    };

    /// This data is stored inside extra, with two sets of trailing `Ref`:
    /// * 0. the then body, according to `then_body_len`.
    /// * 1. the else body, according to `else_body_len`.
    pub const CondBr = struct {
        condition: Ref,
        then_body_len: u32,
        else_body_len: u32,
    };

    /// This data is stored inside extra, trailed by:
    /// * 0. body: Index //  for each `body_len`.
    pub const Try = struct {
        /// The error union to unwrap.
        operand: Ref,
        body_len: u32,
    };

    /// Stored in extra. Depending on the flags in Data, there will be up to 5
    /// trailing Ref fields:
    /// 0. sentinel: Ref // if `has_sentinel` flag is set
    /// 1. align: Ref // if `has_align` flag is set
    /// 2. address_space: Ref // if `has_addrspace` flag is set
    /// 3. bit_start: Ref // if `has_bit_range` flag is set
    /// 4. host_size: Ref // if `has_bit_range` flag is set
    pub const PtrType = struct {
        elem_type: Ref,
        src_node: i32,
    };

    pub const ArrayTypeSentinel = struct {
        len: Ref,
        sentinel: Ref,
        elem_type: Ref,
    };

    pub const SliceStart = struct {
        lhs: Ref,
        start: Ref,
    };

    pub const SliceEnd = struct {
        lhs: Ref,
        start: Ref,
        end: Ref,
    };

    pub const SliceSentinel = struct {
        lhs: Ref,
        start: Ref,
        end: Ref,
        sentinel: Ref,
    };

    /// The meaning of these operands depends on the corresponding `Tag`.
    pub const Bin = struct {
        lhs: Ref,
        rhs: Ref,
    };

    pub const BinNode = struct {
        node: i32,
        lhs: Ref,
        rhs: Ref,
    };

    pub const UnNode = struct {
        node: i32,
        operand: Ref,
    };

    pub const ElemPtrImm = struct {
        ptr: Ref,
        index: u32,
    };

    /// 0. multi_cases_len: u32 // If has_multi_cases is set.
    /// 1. else_body { // If has_else or has_under is set.
    ///        body_len: u32,
    ///        body member Index for every body_len
    ///     }
    /// 2. scalar_cases: { // for every scalar_cases_len
    ///        item: Ref,
    ///        body_len: u32,
    ///        body member Index for every body_len
    ///     }
    /// 3. multi_cases: { // for every multi_cases_len
    ///        items_len: u32,
    ///        ranges_len: u32,
    ///        body_len: u32,
    ///        item: Ref // for every items_len
    ///        ranges: { // for every ranges_len
    ///            item_first: Ref,
    ///            item_last: Ref,
    ///        }
    ///        body member Index for every body_len
    ///    }
    pub const SwitchBlock = struct {
        /// This is always a `switch_cond` or `switch_cond_ref` instruction.
        /// If it is a `switch_cond_ref` instruction, bits.is_ref is always true.
        /// If it is a `switch_cond` instruction, bits.is_ref is always false.
        /// Both `switch_cond` and `switch_cond_ref` return a value, not a pointer,
        /// that is useful for the case items, but cannot be used for capture values.
        /// For the capture values, Sema is expected to find the operand of this operand
        /// and use that.
        operand: Ref,
        bits: Bits,

        pub const Bits = packed struct {
            /// If true, one or more prongs have multiple items.
            has_multi_cases: bool,
            /// If true, there is an else prong. This is mutually exclusive with `has_under`.
            has_else: bool,
            /// If true, there is an underscore prong. This is mutually exclusive with `has_else`.
            has_under: bool,
            scalar_cases_len: ScalarCasesLen,

            pub const ScalarCasesLen = u29;

            pub fn specialProng(bits: Bits) SpecialProng {
                const has_else: u2 = @boolToInt(bits.has_else);
                const has_under: u2 = @boolToInt(bits.has_under);
                return switch ((has_else << 1) | has_under) {
                    0b00 => .none,
                    0b01 => .under,
                    0b10 => .@"else",
                    0b11 => unreachable,
                };
            }
        };

        pub const ScalarProng = struct {
            item: Ref,
            body: []const Index,
        };

        /// TODO performance optimization: instead of having this helper method
        /// change the definition of switch_capture instruction to store extra_index
        /// instead of prong_index. This way, Sema won't be doing O(N^2) iterations
        /// over the switch prongs.
        pub fn getScalarProng(
            self: SwitchBlock,
            zir: Zir,
            extra_end: usize,
            prong_index: usize,
        ) ScalarProng {
            var extra_index: usize = extra_end;

            if (self.bits.has_multi_cases) {
                extra_index += 1;
            }

            if (self.bits.specialProng() != .none) {
                const body_len = @truncate(u31, zir.extra[extra_index]);
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                extra_index += body.len;
            }

            var scalar_i: usize = 0;
            while (true) : (scalar_i += 1) {
                const item = @intToEnum(Ref, zir.extra[extra_index]);
                extra_index += 1;
                const body_len = @truncate(u31, zir.extra[extra_index]);
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                extra_index += body.len;

                if (scalar_i < prong_index) continue;

                return .{
                    .item = item,
                    .body = body,
                };
            }
        }

        pub const MultiProng = struct {
            items: []const Ref,
            body: []const Index,
        };

        pub fn getMultiProng(
            self: SwitchBlock,
            zir: Zir,
            extra_end: usize,
            prong_index: usize,
        ) MultiProng {
            // +1 for self.bits.has_multi_cases == true
            var extra_index: usize = extra_end + 1;

            if (self.bits.specialProng() != .none) {
                const body_len = @truncate(u31, zir.extra[extra_index]);
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                extra_index += body.len;
            }

            var scalar_i: usize = 0;
            while (scalar_i < self.bits.scalar_cases_len) : (scalar_i += 1) {
                extra_index += 1;
                const body_len = @truncate(u31, zir.extra[extra_index]);
                extra_index += 1;
                extra_index += body_len;
            }
            var multi_i: u32 = 0;
            while (true) : (multi_i += 1) {
                const items_len = zir.extra[extra_index];
                extra_index += 1;
                const ranges_len = zir.extra[extra_index];
                extra_index += 1;
                const body_len = @truncate(u31, zir.extra[extra_index]);
                extra_index += 1;
                const items = zir.refSlice(extra_index, items_len);
                extra_index += items_len;
                // Each range has a start and an end.
                extra_index += 2 * ranges_len;

                const body = zir.extra[extra_index..][0..body_len];
                extra_index += body_len;

                if (multi_i < prong_index) continue;
                return .{
                    .items = items,
                    .body = body,
                };
            }
        }
    };

    pub const Field = struct {
        lhs: Ref,
        /// Offset into `string_bytes`.
        field_name_start: u32,
    };

    pub const FieldNamed = struct {
        lhs: Ref,
        field_name: Ref,
    };

    pub const FieldNamedNode = struct {
        node: i32,
        lhs: Ref,
        field_name: Ref,
    };

    pub const As = struct {
        dest_type: Ref,
        operand: Ref,
    };

    /// Trailing:
    /// 0. src_node: i32, // if has_src_node
    /// 1. fields_len: u32, // if has_fields_len
    /// 2. decls_len: u32, // if has_decls_len
    /// 3. backing_int_body_len: u32, // if has_backing_int
    /// 4. backing_int_ref: Ref, // if has_backing_int and backing_int_body_len is 0
    /// 5. backing_int_body_inst: Inst, // if has_backing_int and backing_int_body_len is > 0
    /// 6. decl_bits: u32 // for every 8 decls
    ///    - sets of 4 bits:
    ///      0b000X: whether corresponding decl is pub
    ///      0b00X0: whether corresponding decl is exported
    ///      0b0X00: whether corresponding decl has an align expression
    ///      0bX000: whether corresponding decl has a linksection or an address space expression
    /// 7. decl: { // for every decls_len
    ///        src_hash: [4]u32, // hash of source bytes
    ///        line: u32, // line number of decl, relative to parent
    ///        name: u32, // null terminated string index
    ///        - 0 means comptime or usingnamespace decl.
    ///          - if name == 0 `is_exported` determines which one: 0=comptime,1=usingnamespace
    ///        - 1 means test decl with no name.
    ///        - 2 means that the test is a decltest, doc_comment gives the name of the identifier
    ///        - if there is a 0 byte at the position `name` indexes, it indicates
    ///          this is a test decl, and the name starts at `name+1`.
    ///        value: Index,
    ///        doc_comment: u32, 0 if no doc comment, if this is a decltest, doc_comment references the decl name in the string table
    ///        align: Ref, // if corresponding bit is set
    ///        link_section_or_address_space: { // if corresponding bit is set.
    ///            link_section: Ref,
    ///            address_space: Ref,
    ///        }
    ///    }
    /// 8. flags: u32 // for every 8 fields
    ///    - sets of 4 bits:
    ///      0b000X: whether corresponding field has an align expression
    ///      0b00X0: whether corresponding field has a default expression
    ///      0b0X00: whether corresponding field is comptime
    ///      0bX000: whether corresponding field has a type expression
    /// 9. fields: { // for every fields_len
    ///        field_name: u32, // if !is_tuple
    ///        doc_comment: u32, // 0 if no doc comment
    ///        field_type: Ref, // if corresponding bit is not set. none means anytype.
    ///        field_type_body_len: u32, // if corresponding bit is set
    ///        align_body_len: u32, // if corresponding bit is set
    ///        init_body_len: u32, // if corresponding bit is set
    ///    }
    /// 10. bodies: { // for every fields_len
    ///        field_type_body_inst: Inst, // for each field_type_body_len
    ///        align_body_inst: Inst, // for each align_body_len
    ///        init_body_inst: Inst, // for each init_body_len
    ///    }
    pub const StructDecl = struct {
        pub const Small = packed struct {
            has_src_node: bool,
            has_fields_len: bool,
            has_decls_len: bool,
            has_backing_int: bool,
            known_non_opv: bool,
            known_comptime_only: bool,
            is_tuple: bool,
            name_strategy: NameStrategy,
            layout: std.builtin.Type.ContainerLayout,
            _: u5 = undefined,
        };
    };

    pub const NameStrategy = enum(u2) {
        /// Use the same name as the parent declaration name.
        /// e.g. `const Foo = struct {...};`.
        parent,
        /// Use the name of the currently executing comptime function call,
        /// with the current parameters. e.g. `ArrayList(i32)`.
        func,
        /// Create an anonymous name for this declaration.
        /// Like this: "ParentDeclName_struct_69"
        anon,
        /// Use the name specified in the next `dbg_var_{val,ptr}` instruction.
        dbg_var,
    };

    /// Trailing:
    /// 0. src_node: i32, // if has_src_node
    /// 1. tag_type: Ref, // if has_tag_type
    /// 2. body_len: u32, // if has_body_len
    /// 3. fields_len: u32, // if has_fields_len
    /// 4. decls_len: u32, // if has_decls_len
    /// 5. decl_bits: u32 // for every 8 decls
    ///    - sets of 4 bits:
    ///      0b000X: whether corresponding decl is pub
    ///      0b00X0: whether corresponding decl is exported
    ///      0b0X00: whether corresponding decl has an align expression
    ///      0bX000: whether corresponding decl has a linksection or an address space expression
    /// 6. decl: { // for every decls_len
    ///        src_hash: [4]u32, // hash of source bytes
    ///        line: u32, // line number of decl, relative to parent
    ///        name: u32, // null terminated string index
    ///        - 0 means comptime or usingnamespace decl.
    ///          - if name == 0 `is_exported` determines which one: 0=comptime,1=usingnamespace
    ///        - 1 means test decl with no name.
    ///        - if there is a 0 byte at the position `name` indexes, it indicates
    ///          this is a test decl, and the name starts at `name+1`.
    ///        value: Index,
    ///        doc_comment: u32, // 0 if no doc_comment
    ///        align: Ref, // if corresponding bit is set
    ///        link_section_or_address_space: { // if corresponding bit is set.
    ///            link_section: Ref,
    ///            address_space: Ref,
    ///        }
    ///    }
    /// 7. inst: Index // for every body_len
    /// 8. has_bits: u32 // for every 32 fields
    ///    - the bit is whether corresponding field has an value expression
    /// 9. fields: { // for every fields_len
    ///        field_name: u32,
    ///        doc_comment: u32, // 0 if no doc_comment
    ///        value: Ref, // if corresponding bit is set
    ///    }
    pub const EnumDecl = struct {
        pub const Small = packed struct {
            has_src_node: bool,
            has_tag_type: bool,
            has_body_len: bool,
            has_fields_len: bool,
            has_decls_len: bool,
            name_strategy: NameStrategy,
            nonexhaustive: bool,
            _: u8 = undefined,
        };
    };

    /// Trailing:
    /// 0. src_node: i32, // if has_src_node
    /// 1. tag_type: Ref, // if has_tag_type
    /// 2. body_len: u32, // if has_body_len
    /// 3. fields_len: u32, // if has_fields_len
    /// 4. decls_len: u32, // if has_decls_len
    /// 5. decl_bits: u32 // for every 8 decls
    ///    - sets of 4 bits:
    ///      0b000X: whether corresponding decl is pub
    ///      0b00X0: whether corresponding decl is exported
    ///      0b0X00: whether corresponding decl has an align expression
    ///      0bX000: whether corresponding decl has a linksection or an address space expression
    /// 6. decl: { // for every decls_len
    ///        src_hash: [4]u32, // hash of source bytes
    ///        line: u32, // line number of decl, relative to parent
    ///        name: u32, // null terminated string index
    ///        - 0 means comptime or usingnamespace decl.
    ///          - if name == 0 `is_exported` determines which one: 0=comptime,1=usingnamespace
    ///        - 1 means test decl with no name.
    ///        - if there is a 0 byte at the position `name` indexes, it indicates
    ///          this is a test decl, and the name starts at `name+1`.
    ///        value: Index,
    ///        doc_comment: u32, // 0 if no doc comment
    ///        align: Ref, // if corresponding bit is set
    ///        link_section_or_address_space: { // if corresponding bit is set.
    ///            link_section: Ref,
    ///            address_space: Ref,
    ///        }
    ///    }
    /// 7. inst: Index // for every body_len
    /// 8. has_bits: u32 // for every 8 fields
    ///    - sets of 4 bits:
    ///      0b000X: whether corresponding field has a type expression
    ///      0b00X0: whether corresponding field has a align expression
    ///      0b0X00: whether corresponding field has a tag value expression
    ///      0bX000: unused
    /// 9. fields: { // for every fields_len
    ///        field_name: u32, // null terminated string index
    ///        doc_comment: u32, // 0 if no doc comment
    ///        field_type: Ref, // if corresponding bit is set
    ///        - if none, means `anytype`.
    ///        align: Ref, // if corresponding bit is set
    ///        tag_value: Ref, // if corresponding bit is set
    ///    }
    pub const UnionDecl = struct {
        pub const Small = packed struct {
            has_src_node: bool,
            has_tag_type: bool,
            has_body_len: bool,
            has_fields_len: bool,
            has_decls_len: bool,
            name_strategy: NameStrategy,
            layout: std.builtin.Type.ContainerLayout,
            /// has_tag_type | auto_enum_tag | result
            /// -------------------------------------
            ///    false     | false         |  union { }
            ///    false     | true          |  union(enum) { }
            ///    true      | true          |  union(enum(T)) { }
            ///    true      | false         |  union(T) { }
            auto_enum_tag: bool,
            _: u6 = undefined,
        };
    };

    /// Trailing:
    /// 0. src_node: i32, // if has_src_node
    /// 1. decls_len: u32, // if has_decls_len
    /// 2. decl_bits: u32 // for every 8 decls
    ///    - sets of 4 bits:
    ///      0b000X: whether corresponding decl is pub
    ///      0b00X0: whether corresponding decl is exported
    ///      0b0X00: whether corresponding decl has an align expression
    ///      0bX000: whether corresponding decl has a linksection or an address space expression
    /// 3. decl: { // for every decls_len
    ///        src_hash: [4]u32, // hash of source bytes
    ///        line: u32, // line number of decl, relative to parent
    ///        name: u32, // null terminated string index
    ///        - 0 means comptime or usingnamespace decl.
    ///          - if name == 0 `is_exported` determines which one: 0=comptime,1=usingnamespace
    ///        - 1 means test decl with no name.
    ///        - if there is a 0 byte at the position `name` indexes, it indicates
    ///          this is a test decl, and the name starts at `name+1`.
    ///        value: Index,
    ///        doc_comment: u32, // 0 if no doc comment,
    ///        align: Ref, // if corresponding bit is set
    ///        link_section_or_address_space: { // if corresponding bit is set.
    ///            link_section: Ref,
    ///            address_space: Ref,
    ///        }
    ///    }
    pub const OpaqueDecl = struct {
        pub const Small = packed struct {
            has_src_node: bool,
            has_decls_len: bool,
            name_strategy: NameStrategy,
            _: u12 = undefined,
        };
    };

    /// Trailing:
    /// { // for every fields_len
    ///      field_name: u32 // null terminated string index
    ///     doc_comment: u32 // null terminated string index
    /// }
    pub const ErrorSetDecl = struct {
        fields_len: u32,
    };

    /// A f128 value, broken up into 4 u32 parts.
    pub const Float128 = struct {
        piece0: u32,
        piece1: u32,
        piece2: u32,
        piece3: u32,

        pub fn get(self: Float128) f128 {
            const int_bits = @as(u128, self.piece0) |
                (@as(u128, self.piece1) << 32) |
                (@as(u128, self.piece2) << 64) |
                (@as(u128, self.piece3) << 96);
            return @bitCast(f128, int_bits);
        }
    };

    /// Trailing is an item per field.
    pub const StructInit = struct {
        fields_len: u32,

        pub const Item = struct {
            /// The `field_type` ZIR instruction for this field init.
            field_type: Index,
            /// The field init expression to be used as the field value.
            init: Ref,
        };
    };

    /// Trailing is an Item per field.
    /// TODO make this instead array of inits followed by array of names because
    /// it will be simpler Sema code and better for CPU cache.
    pub const StructInitAnon = struct {
        fields_len: u32,

        pub const Item = struct {
            /// Null-terminated string table index.
            field_name: u32,
            /// The field init expression to be used as the field value.
            init: Ref,
        };
    };

    pub const FieldType = struct {
        container_type: Ref,
        /// Offset into `string_bytes`, null terminated.
        name_start: u32,
    };

    pub const FieldTypeRef = struct {
        container_type: Ref,
        field_name: Ref,
    };

    pub const Cmpxchg = struct {
        node: i32,
        ptr: Ref,
        expected_value: Ref,
        new_value: Ref,
        success_order: Ref,
        failure_order: Ref,
    };

    pub const AtomicRmw = struct {
        ptr: Ref,
        operation: Ref,
        operand: Ref,
        ordering: Ref,
    };

    pub const UnionInit = struct {
        union_type: Ref,
        field_name: Ref,
        init: Ref,
    };

    pub const AtomicStore = struct {
        ptr: Ref,
        operand: Ref,
        ordering: Ref,
    };

    pub const AtomicLoad = struct {
        elem_type: Ref,
        ptr: Ref,
        ordering: Ref,
    };

    pub const MulAdd = struct {
        mulend1: Ref,
        mulend2: Ref,
        addend: Ref,
    };

    pub const FieldParentPtr = struct {
        parent_type: Ref,
        field_name: Ref,
        field_ptr: Ref,
    };

    pub const Shuffle = struct {
        elem_type: Ref,
        a: Ref,
        b: Ref,
        mask: Ref,
    };

    pub const Select = struct {
        node: i32,
        elem_type: Ref,
        pred: Ref,
        a: Ref,
        b: Ref,
    };

    pub const AsyncCall = struct {
        node: i32,
        frame_buffer: Ref,
        result_ptr: Ref,
        fn_ptr: Ref,
        args: Ref,
    };

    /// Trailing: inst: Index // for every body_len
    pub const Param = struct {
        /// Null-terminated string index.
        name: u32,
        /// 0 if no doc comment
        doc_comment: u32,
        /// The body contains the type of the parameter.
        body_len: u32,
    };

    /// Trailing:
    /// 0. type_inst: Ref,  // if small 0b000X is set
    /// 1. align_inst: Ref, // if small 0b00X0 is set
    pub const AllocExtended = struct {
        src_node: i32,

        pub const Small = packed struct {
            has_type: bool,
            has_align: bool,
            is_const: bool,
            is_comptime: bool,
            _: u12 = undefined,
        };
    };

    pub const Export = struct {
        /// If present, this is referring to a Decl via field access, e.g. `a.b`.
        /// If omitted, this is referring to a Decl via identifier, e.g. `a`.
        namespace: Ref,
        /// Null-terminated string index.
        decl_name: u32,
        options: Ref,
    };

    pub const ExportValue = struct {
        /// The comptime value to export.
        operand: Ref,
        options: Ref,
    };

    /// Trailing: `CompileErrors.Item` for each `items_len`.
    pub const CompileErrors = struct {
        items_len: u32,

        /// Trailing: `note_payload_index: u32` for each `notes_len`.
        /// It's a payload index of another `Item`.
        pub const Item = struct {
            /// null terminated string index
            msg: u32,
            node: Ast.Node.Index,
            /// If node is 0 then this will be populated.
            token: Ast.TokenIndex,
            /// Can be used in combination with `token`.
            byte_offset: u32,
            /// 0 or a payload index of a `Block`, each is a payload
            /// index of another `Item`.
            notes: u32,

            pub fn notesLen(item: Item, zir: Zir) u32 {
                if (item.notes == 0) return 0;
                const block = zir.extraData(Block, item.notes);
                return block.data.body_len;
            }
        };
    };

    /// Trailing: for each `imports_len` there is an Item
    pub const Imports = struct {
        imports_len: Inst.Index,

        pub const Item = struct {
            /// null terminated string index
            name: u32,
            /// points to the import name
            token: Ast.TokenIndex,
        };
    };

    pub const LineColumn = struct {
        line: u32,
        column: u32,
    };

    pub const ArrayInit = struct {
        ty: Ref,
        init_count: u32,
    };

    pub const Src = struct {
        node: i32,
        line: u32,
        column: u32,
    };

    pub const DeferErrCode = struct {
        remapped_err_code: Index,
        index: u32,
        len: u32,
    };

    pub fn isNoReturn(self: Inst) bool {
        return switch (self) {
            .param,
            .param_comptime,
            .param_anytype,
            .param_anytype_comptime,
            .add,
            .addwrap,
            .add_sat,
            .add_unsafe,
            .alloc,
            .alloc_mut,
            .alloc_comptime_mut,
            .alloc_inferred,
            .alloc_inferred_mut,
            .alloc_inferred_comptime,
            .alloc_inferred_comptime_mut,
            .make_ptr_const,
            .array_cat,
            .array_mul,
            .array_type,
            .array_type_sentinel,
            .vector_type,
            .elem_type_index,
            .indexable_ptr_len,
            .anyframe_type,
            .as,
            .as_node,
            .as_shift_operand,
            .bit_and,
            .bitcast,
            .bit_or,
            .block,
            .block_comptime,
            .block_inline,
            .suspend_block,
            .loop,
            .bool_br_and,
            .bool_br_or,
            .bool_not,
            .call,
            .cmp_lt,
            .cmp_lte,
            .cmp_eq,
            .cmp_gte,
            .cmp_gt,
            .cmp_neq,
            .coerce_result_ptr,
            .error_set_decl,
            .error_set_decl_anon,
            .error_set_decl_func,
            .dbg_stmt,
            .dbg_var_ptr,
            .dbg_var_val,
            .dbg_block_begin,
            .dbg_block_end,
            .decl_ref,
            .decl_val,
            .load,
            .div,
            .elem_ptr,
            .elem_val,
            .elem_ptr_node,
            .elem_ptr_imm,
            .elem_val_node,
            .ensure_result_used,
            .ensure_result_non_error,
            .ensure_err_union_payload_void,
            .@"export",
            .export_value,
            .field_ptr,
            .field_ptr_init,
            .field_val,
            .field_call_bind,
            .field_ptr_named,
            .field_val_named,
            .func,
            .func_inferred,
            .func_fancy,
            .has_decl,
            .int,
            .int_big,
            .float,
            .float128,
            .int_type,
            .is_non_null,
            .is_non_null_ptr,
            .is_non_err,
            .is_non_err_ptr,
            .ret_is_non_err,
            .mod_rem,
            .mul,
            .mulwrap,
            .mul_sat,
            .ref,
            .shl,
            .shl_sat,
            .shr,
            .store,
            .store_node,
            .store_to_block_ptr,
            .store_to_inferred_ptr,
            .str,
            .sub,
            .subwrap,
            .sub_sat,
            .negate,
            .negate_wrap,
            .typeof,
            .typeof_builtin,
            .xor,
            .optional_type,
            .optional_payload_safe,
            .optional_payload_unsafe,
            .optional_payload_safe_ptr,
            .optional_payload_unsafe_ptr,
            .err_union_payload_unsafe,
            .err_union_payload_unsafe_ptr,
            .err_union_code,
            .err_union_code_ptr,
            .ptr_type,
            .enum_literal,
            .merge_error_sets,
            .error_union_type,
            .bit_not,
            .error_value,
            .slice_start,
            .slice_end,
            .slice_sentinel,
            .import,
            .typeof_log2_int_type,
            .resolve_inferred_alloc,
            .set_eval_branch_quota,
            .switch_capture,
            .switch_capture_ref,
            .switch_capture_multi,
            .switch_capture_multi_ref,
            .switch_capture_tag,
            .switch_block,
            .switch_cond,
            .switch_cond_ref,
            .array_base_ptr,
            .field_base_ptr,
            .validate_array_init_ty,
            .validate_struct_init_ty,
            .validate_struct_init,
            .validate_array_init,
            .validate_deref,
            .struct_init_empty,
            .struct_init,
            .struct_init_ref,
            .struct_init_anon,
            .struct_init_anon_ref,
            .array_init,
            .array_init_anon,
            .array_init_ref,
            .array_init_anon_ref,
            .union_init,
            .field_type,
            .field_type_ref,
            .int_to_enum,
            .enum_to_int,
            .type_info,
            .size_of,
            .bit_size_of,
            .ptr_to_int,
            .align_of,
            .bool_to_int,
            .embed_file,
            .error_name,
            .set_runtime_safety,
            .sqrt,
            .sin,
            .cos,
            .tan,
            .exp,
            .exp2,
            .log,
            .log2,
            .log10,
            .fabs,
            .floor,
            .ceil,
            .trunc,
            .round,
            .tag_name,
            .type_name,
            .frame_type,
            .frame_size,
            .float_to_int,
            .int_to_float,
            .int_to_ptr,
            .float_cast,
            .int_cast,
            .ptr_cast,
            .truncate,
            .align_cast,
            .has_field,
            .clz,
            .ctz,
            .pop_count,
            .byte_swap,
            .bit_reverse,
            .div_exact,
            .div_floor,
            .div_trunc,
            .mod,
            .rem,
            .shl_exact,
            .shr_exact,
            .bit_offset_of,
            .offset_of,
            .splat,
            .reduce,
            .shuffle,
            .atomic_load,
            .atomic_rmw,
            .atomic_store,
            .mul_add,
            .builtin_call,
            .field_parent_ptr,
            .max,
            .memcpy,
            .memset,
            .min,
            .c_import,
            .@"resume",
            .@"await",
            .ret_err_value_code,
            .extended,
            .closure_get,
            .closure_capture,
            .ret_ptr,
            .ret_type,
            .@"try",
            .try_ptr,
            .@"defer",
            .defer_err_code,
            .save_err_ret_index,
            .restore_err_ret_index,
            .for_len,
            => false,

            .@"break",
            .break_inline,
            .condbr,
            .condbr_inline,
            .compile_error,
            .ret_node,
            .ret_load,
            .ret_implicit,
            .ret_err_value,
            .@"unreachable",
            .repeat,
            .repeat_inline,
            .panic,
            .trap,
            .check_comptime_control_flow,
            => true,
        };
    }

    pub fn isAlwaysVoid(self: Inst) bool {
        return switch (self) {
            .dbg_stmt,
            .dbg_var_ptr,
            .dbg_var_val,
            .dbg_block_begin,
            .dbg_block_end,
            .ensure_result_used,
            .ensure_result_non_error,
            .ensure_err_union_payload_void,
            .set_eval_branch_quota,
            .atomic_store,
            .store,
            .store_node,
            .store_to_block_ptr,
            .store_to_inferred_ptr,
            .resolve_inferred_alloc,
            .validate_array_init_ty,
            .validate_struct_init_ty,
            .validate_struct_init,
            .validate_array_init,
            .validate_deref,
            .@"export",
            .export_value,
            .set_runtime_safety,
            .memcpy,
            .memset,
            .check_comptime_control_flow,
            .@"defer",
            .defer_err_code,
            .restore_err_ret_index,
            .save_err_ret_index,
            => true,

            .param,
            .param_comptime,
            .param_anytype,
            .param_anytype_comptime,
            .add,
            .addwrap,
            .add_sat,
            .add_unsafe,
            .alloc,
            .alloc_mut,
            .alloc_comptime_mut,
            .alloc_inferred,
            .alloc_inferred_mut,
            .alloc_inferred_comptime,
            .alloc_inferred_comptime_mut,
            .make_ptr_const,
            .array_cat,
            .array_mul,
            .array_type,
            .array_type_sentinel,
            .vector_type,
            .elem_type_index,
            .indexable_ptr_len,
            .anyframe_type,
            .as,
            .as_node,
            .as_shift_operand,
            .bit_and,
            .bitcast,
            .bit_or,
            .block,
            .block_comptime,
            .block_inline,
            .suspend_block,
            .loop,
            .bool_br_and,
            .bool_br_or,
            .bool_not,
            .call,
            .cmp_lt,
            .cmp_lte,
            .cmp_eq,
            .cmp_gte,
            .cmp_gt,
            .cmp_neq,
            .coerce_result_ptr,
            .error_set_decl,
            .error_set_decl_anon,
            .error_set_decl_func,
            .decl_ref,
            .decl_val,
            .load,
            .div,
            .elem_ptr,
            .elem_val,
            .elem_ptr_node,
            .elem_ptr_imm,
            .elem_val_node,
            .field_ptr,
            .field_ptr_init,
            .field_val,
            .field_call_bind,
            .field_ptr_named,
            .field_val_named,
            .func,
            .func_inferred,
            .func_fancy,
            .has_decl,
            .int,
            .int_big,
            .float,
            .float128,
            .int_type,
            .is_non_null,
            .is_non_null_ptr,
            .is_non_err,
            .is_non_err_ptr,
            .ret_is_non_err,
            .mod_rem,
            .mul,
            .mulwrap,
            .mul_sat,
            .ref,
            .shl,
            .shl_sat,
            .shr,
            .str,
            .sub,
            .subwrap,
            .sub_sat,
            .negate,
            .negate_wrap,
            .typeof,
            .typeof_builtin,
            .xor,
            .optional_type,
            .optional_payload_safe,
            .optional_payload_unsafe,
            .optional_payload_safe_ptr,
            .optional_payload_unsafe_ptr,
            .err_union_payload_unsafe,
            .err_union_payload_unsafe_ptr,
            .err_union_code,
            .err_union_code_ptr,
            .ptr_type,
            .enum_literal,
            .merge_error_sets,
            .error_union_type,
            .bit_not,
            .error_value,
            .slice_start,
            .slice_end,
            .slice_sentinel,
            .import,
            .typeof_log2_int_type,
            .switch_capture,
            .switch_capture_ref,
            .switch_capture_multi,
            .switch_capture_multi_ref,
            .switch_capture_tag,
            .switch_block,
            .switch_cond,
            .switch_cond_ref,
            .array_base_ptr,
            .field_base_ptr,
            .struct_init_empty,
            .struct_init,
            .struct_init_ref,
            .struct_init_anon,
            .struct_init_anon_ref,
            .array_init,
            .array_init_anon,
            .array_init_ref,
            .array_init_anon_ref,
            .union_init,
            .field_type,
            .field_type_ref,
            .int_to_enum,
            .enum_to_int,
            .type_info,
            .size_of,
            .bit_size_of,
            .ptr_to_int,
            .align_of,
            .bool_to_int,
            .embed_file,
            .error_name,
            .sqrt,
            .sin,
            .cos,
            .tan,
            .exp,
            .exp2,
            .log,
            .log2,
            .log10,
            .fabs,
            .floor,
            .ceil,
            .trunc,
            .round,
            .tag_name,
            .type_name,
            .frame_type,
            .frame_size,
            .float_to_int,
            .int_to_float,
            .int_to_ptr,
            .float_cast,
            .int_cast,
            .ptr_cast,
            .truncate,
            .align_cast,
            .has_field,
            .clz,
            .ctz,
            .pop_count,
            .byte_swap,
            .bit_reverse,
            .div_exact,
            .div_floor,
            .div_trunc,
            .mod,
            .rem,
            .shl_exact,
            .shr_exact,
            .bit_offset_of,
            .offset_of,
            .splat,
            .reduce,
            .shuffle,
            .atomic_load,
            .atomic_rmw,
            .mul_add,
            .builtin_call,
            .field_parent_ptr,
            .max,
            .min,
            .c_import,
            .@"resume",
            .@"await",
            .ret_err_value_code,
            .closure_get,
            .closure_capture,
            .@"break",
            .break_inline,
            .condbr,
            .condbr_inline,
            .compile_error,
            .ret_node,
            .ret_load,
            .ret_implicit,
            .ret_err_value,
            .ret_ptr,
            .ret_type,
            .@"unreachable",
            .repeat,
            .repeat_inline,
            .panic,
            .trap,
            .for_len,
            .@"try",
            .try_ptr,
            => false,

            .extended => |extended| switch (extended.opcode) {
                .fence, .set_cold, .breakpoint => true,
                else => false,
            },
        };
    }

    /// Asserts that `tag` actually has a PayloadNode.
    pub fn makePayloadNode(tag: Tag, pl_node: PayloadNode) Inst {
        return switch (tag) {
            inline .add,
            .addwrap,
            .add_sat,
            .add_unsafe,
            .sub,
            .subwrap,
            .sub_sat,
            .mul,
            .mulwrap,
            .mul_sat,
            .div_exact,
            .div_floor,
            .div_trunc,
            .mod,
            .rem,
            .mod_rem,
            .shl,
            .shl_exact,
            .shl_sat,
            .shr,
            .shr_exact,
            .array_cat,
            .array_mul,
            .array_type,
            .array_type_sentinel,
            .vector_type,
            .as_node,
            .as_shift_operand,
            .bit_and,
            .bitcast,
            .bit_or,
            .block,
            .block_comptime,
            .block_inline,
            .suspend_block,
            .call,
            .builtin_call,
            .cmp_lt,
            .cmp_lte,
            .cmp_eq,
            .cmp_gte,
            .cmp_gt,
            .cmp_neq,
            .coerce_result_ptr,
            .condbr,
            .condbr_inline,
            .@"try",
            .try_ptr,
            .error_set_decl,
            .error_set_decl_anon,
            .error_set_decl_func,
            .div,
            .elem_ptr_node,
            .elem_ptr,
            .elem_ptr_imm,
            .elem_val_node,
            .elem_val,
            .error_union_type,
            .@"export",
            .export_value,
            .field_ptr,
            .field_ptr_init,
            .field_val,
            .field_call_bind,
            .field_ptr_named,
            .field_val_named,
            .func,
            .func_inferred,
            .func_fancy,
            .float128,
            .loop,
            .for_len,
            .merge_error_sets,
            .slice_start,
            .slice_end,
            .slice_sentinel,
            .store_node,
            .typeof_builtin,
            .xor,
            .switch_block,
            .validate_array_init_ty,
            .validate_struct_init,
            .validate_array_init,
            .field_type,
            .field_type_ref,
            .struct_init,
            .struct_init_ref,
            .struct_init_anon,
            .struct_init_anon_ref,
            .array_init,
            .array_init_anon,
            .array_init_ref,
            .array_init_anon_ref,
            .union_init,
            .float_to_int,
            .int_to_float,
            .int_to_ptr,
            .int_to_enum,
            .float_cast,
            .int_cast,
            .ptr_cast,
            .truncate,
            .align_cast,
            .has_decl,
            .has_field,
            .bit_offset_of,
            .offset_of,
            .splat,
            .reduce,
            .shuffle,
            .atomic_load,
            .atomic_rmw,
            .atomic_store,
            .mul_add,
            .field_parent_ptr,
            .memcpy,
            .memset,
            .min,
            .max,
            .c_import,
            => |t| @unionInit(Inst, @tagName(t), pl_node),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has a UnaryNode.
    pub fn makeUnaryNode(tag: Tag, un_node: UnaryNode) Inst {
        return switch (tag) {
            inline .indexable_ptr_len,
            .anyframe_type,
            .bit_not,
            .bool_not,
            .check_comptime_control_flow,
            .load,
            .ensure_result_used,
            .ensure_result_non_error,
            .ensure_err_union_payload_void,
            .is_non_null,
            .is_non_null_ptr,
            .is_non_err,
            .is_non_err_ptr,
            .ret_is_non_err,
            .ret_node,
            .ret_load,
            .negate,
            .negate_wrap,
            .typeof,
            .typeof_log2_int_type,
            .optional_type,
            .optional_payload_safe,
            .optional_payload_unsafe,
            .optional_payload_safe_ptr,
            .optional_payload_unsafe_ptr,
            .err_union_payload_unsafe,
            .err_union_payload_unsafe_ptr,
            .err_union_code,
            .err_union_code_ptr,
            .switch_cond,
            .switch_cond_ref,
            .array_base_ptr,
            .field_base_ptr,
            .validate_struct_init_ty,
            .validate_deref,
            .struct_init_empty,
            .type_info,
            .size_of,
            .bit_size_of,
            .ptr_to_int,
            .compile_error,
            .set_eval_branch_quota,
            .enum_to_int,
            .align_of,
            .bool_to_int,
            .embed_file,
            .error_name,
            .panic,
            .set_runtime_safety,
            .sqrt,
            .sin,
            .cos,
            .tan,
            .exp,
            .exp2,
            .log,
            .log2,
            .log10,
            .fabs,
            .floor,
            .ceil,
            .trunc,
            .round,
            .tag_name,
            .type_name,
            .frame_type,
            .frame_size,
            .clz,
            .ctz,
            .pop_count,
            .byte_swap,
            .bit_reverse,
            .alloc,
            .alloc_mut,
            .alloc_comptime_mut,
            .resolve_inferred_alloc,
            .make_ptr_const,
            .@"resume",
            .@"await",
            => |t| @unionInit(Inst, @tagName(t), un_node),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has a UnaryToken.
    pub fn makeUnaryToken(tag: Tag, un_tok: UnaryToken) Inst {
        return switch (tag) {
            inline .ref,
            .ret_implicit,
            .switch_capture_tag,
            .closure_capture,
            => |t| @unionInit(Inst, @tagName(t), un_tok),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has a StringToken.
    pub fn makeStringToken(tag: Tag, str_tok: StringToken) Inst {
        return switch (tag) {
            inline .param_anytype,
            .param_anytype_comptime,
            .decl_ref,
            .decl_val,
            .error_value,
            .import,
            .ret_err_value,
            .ret_err_value_code,
            .enum_literal,
            => |t| @unionInit(Inst, @tagName(t), str_tok),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has a BoolBreak.
    pub fn makeBoolBreak(tag: Tag, bool_br: BoolBreak) Inst {
        return switch (tag) {
            inline .bool_br_and, .bool_br_or => |t| @unionInit(Inst, @tagName(t), bool_br),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has a BreakNode.
    pub fn makeBreakNode(tag: Tag, break_node: BreakNode) Inst {
        return switch (tag) {
            inline .@"break", .break_inline => |t| @unionInit(Inst, @tagName(t), break_node),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has a Bin.
    pub fn makeBin(tag: Tag, bin: Bin) Inst {
        return switch (tag) {
            inline .elem_type_index,
            .as,
            .store,
            .store_to_block_ptr,
            .store_to_inferred_ptr,
            => |t| @unionInit(Inst, @tagName(t), bin),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has an i32.
    pub fn makeNode(tag: Tag, node: i32) Inst {
        return switch (tag) {
            inline .repeat,
            .repeat_inline,
            .ret_ptr,
            .ret_type,
            .trap,
            .alloc_inferred,
            .alloc_inferred_mut,
            .alloc_inferred_comptime,
            .alloc_inferred_comptime_mut,
            => |t| @unionInit(Inst, @tagName(t), node),
            else => unreachable,
        };
    }

    /// Asserts that `tag` actually has an InstNode.
    pub fn makeInstNode(tag: Tag, inst_node: InstNode) Inst {
        return switch (tag) {
            inline .closure_get => |t| @unionInit(Inst, @tagName(t), inst_node),
            else => unreachable,
        };
    }
};

pub const SpecialProng = enum { none, @"else", under };

pub const DeclIterator = struct {
    extra_index: usize,
    bit_bag_index: usize,
    cur_bit_bag: u32,
    decl_i: u32,
    decls_len: u32,
    zir: Zir,

    pub const Item = struct {
        name: [:0]const u8,
        sub_index: u32,
        flags: u4,
    };

    pub fn next(it: *DeclIterator) ?Item {
        if (it.decl_i >= it.decls_len) return null;

        if (it.decl_i % 8 == 0) {
            it.cur_bit_bag = it.zir.extra[it.bit_bag_index];
            it.bit_bag_index += 1;
        }
        it.decl_i += 1;

        const flags = @truncate(u4, it.cur_bit_bag);
        it.cur_bit_bag >>= 4;

        const sub_index = @intCast(u32, it.extra_index);
        it.extra_index += 5; // src_hash(4) + line(1)
        const name = it.zir.nullTerminatedString(it.zir.extra[it.extra_index]);
        it.extra_index += 3; // name(1) + value(1) + doc_comment(1)
        it.extra_index += @truncate(u1, flags >> 2);
        it.extra_index += @truncate(u1, flags >> 3);

        return Item{
            .sub_index = sub_index,
            .name = name,
            .flags = flags,
        };
    }
};

pub fn declIterator(zir: Zir, decl_inst: u32) DeclIterator {
    const tags = zir.instructions.items(.tags);
    const datas = zir.instructions.items(.data);
    switch (tags[decl_inst]) {
        // Functions are allowed and yield no iterations.
        // There is one case matching this in the extended instruction set below.
        .func, .func_inferred, .func_fancy => return declIteratorInner(zir, 0, 0),

        .extended => {
            const extended = datas[decl_inst].extended;
            switch (extended.opcode) {
                .struct_decl => {
                    const small = @bitCast(Inst.StructDecl.Small, extended.small);
                    var extra_index: usize = extended.operand;
                    extra_index += @boolToInt(small.has_src_node);
                    extra_index += @boolToInt(small.has_fields_len);
                    const decls_len = if (small.has_decls_len) decls_len: {
                        const decls_len = zir.extra[extra_index];
                        extra_index += 1;
                        break :decls_len decls_len;
                    } else 0;

                    if (small.has_backing_int) {
                        const backing_int_body_len = zir.extra[extra_index];
                        extra_index += 1; // backing_int_body_len
                        if (backing_int_body_len == 0) {
                            extra_index += 1; // backing_int_ref
                        } else {
                            extra_index += backing_int_body_len; // backing_int_body_inst
                        }
                    }

                    return declIteratorInner(zir, extra_index, decls_len);
                },
                .enum_decl => {
                    const small = @bitCast(Inst.EnumDecl.Small, extended.small);
                    var extra_index: usize = extended.operand;
                    extra_index += @boolToInt(small.has_src_node);
                    extra_index += @boolToInt(small.has_tag_type);
                    extra_index += @boolToInt(small.has_body_len);
                    extra_index += @boolToInt(small.has_fields_len);
                    const decls_len = if (small.has_decls_len) decls_len: {
                        const decls_len = zir.extra[extra_index];
                        extra_index += 1;
                        break :decls_len decls_len;
                    } else 0;

                    return declIteratorInner(zir, extra_index, decls_len);
                },
                .union_decl => {
                    const small = @bitCast(Inst.UnionDecl.Small, extended.small);
                    var extra_index: usize = extended.operand;
                    extra_index += @boolToInt(small.has_src_node);
                    extra_index += @boolToInt(small.has_tag_type);
                    extra_index += @boolToInt(small.has_body_len);
                    extra_index += @boolToInt(small.has_fields_len);
                    const decls_len = if (small.has_decls_len) decls_len: {
                        const decls_len = zir.extra[extra_index];
                        extra_index += 1;
                        break :decls_len decls_len;
                    } else 0;

                    return declIteratorInner(zir, extra_index, decls_len);
                },
                .opaque_decl => {
                    const small = @bitCast(Inst.OpaqueDecl.Small, extended.small);
                    var extra_index: usize = extended.operand;
                    extra_index += @boolToInt(small.has_src_node);
                    const decls_len = if (small.has_decls_len) decls_len: {
                        const decls_len = zir.extra[extra_index];
                        extra_index += 1;
                        break :decls_len decls_len;
                    } else 0;

                    return declIteratorInner(zir, extra_index, decls_len);
                },
                else => unreachable,
            }
        },
        else => unreachable,
    }
}

pub fn declIteratorInner(zir: Zir, extra_index: usize, decls_len: u32) DeclIterator {
    const bit_bags_count = std.math.divCeil(usize, decls_len, 8) catch unreachable;
    return .{
        .zir = zir,
        .extra_index = extra_index + bit_bags_count,
        .bit_bag_index = extra_index,
        .cur_bit_bag = undefined,
        .decl_i = 0,
        .decls_len = decls_len,
    };
}

/// The iterator would have to allocate memory anyway to iterate. So here we populate
/// an ArrayList as the result.
pub fn findDecls(zir: Zir, list: *std.ArrayList(Inst.Index), decl_sub_index: u32) !void {
    const block_inst = zir.extra[decl_sub_index + 6];
    list.clearRetainingCapacity();

    return zir.findDeclsInner(list, block_inst);
}

fn findDeclsInner(
    zir: Zir,
    list: *std.ArrayList(Inst.Index),
    inst: Inst.Index,
) Allocator.Error!void {
    const tags = zir.instructions.items(.tags);
    const datas = zir.instructions.items(.data);

    switch (tags[inst]) {
        // Functions instructions are interesting and have a body.
        .func,
        .func_inferred,
        => {
            try list.append(inst);

            const inst_data = datas[inst].pl_node;
            const extra = zir.extraData(Inst.Func, inst_data.payload_index);
            var extra_index: usize = extra.end;
            switch (extra.data.ret_body_len) {
                0 => {},
                1 => extra_index += 1,
                else => {
                    const body = zir.extra[extra_index..][0..extra.data.ret_body_len];
                    extra_index += body.len;
                    try zir.findDeclsBody(list, body);
                },
            }
            const body = zir.extra[extra_index..][0..extra.data.body_len];
            return zir.findDeclsBody(list, body);
        },
        .func_fancy => {
            try list.append(inst);

            const inst_data = datas[inst].pl_node;
            const extra = zir.extraData(Inst.FuncFancy, inst_data.payload_index);
            var extra_index: usize = extra.end;
            extra_index += @boolToInt(extra.data.bits.has_lib_name);

            if (extra.data.bits.has_align_body) {
                const body_len = zir.extra[extra_index];
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                try zir.findDeclsBody(list, body);
                extra_index += body.len;
            } else if (extra.data.bits.has_align_ref) {
                extra_index += 1;
            }

            if (extra.data.bits.has_addrspace_body) {
                const body_len = zir.extra[extra_index];
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                try zir.findDeclsBody(list, body);
                extra_index += body.len;
            } else if (extra.data.bits.has_addrspace_ref) {
                extra_index += 1;
            }

            if (extra.data.bits.has_section_body) {
                const body_len = zir.extra[extra_index];
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                try zir.findDeclsBody(list, body);
                extra_index += body.len;
            } else if (extra.data.bits.has_section_ref) {
                extra_index += 1;
            }

            if (extra.data.bits.has_cc_body) {
                const body_len = zir.extra[extra_index];
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                try zir.findDeclsBody(list, body);
                extra_index += body.len;
            } else if (extra.data.bits.has_cc_ref) {
                extra_index += 1;
            }

            if (extra.data.bits.has_ret_ty_body) {
                const body_len = zir.extra[extra_index];
                extra_index += 1;
                const body = zir.extra[extra_index..][0..body_len];
                try zir.findDeclsBody(list, body);
                extra_index += body.len;
            } else if (extra.data.bits.has_ret_ty_ref) {
                extra_index += 1;
            }

            extra_index += @boolToInt(extra.data.bits.has_any_noalias);

            const body = zir.extra[extra_index..][0..extra.data.body_len];
            return zir.findDeclsBody(list, body);
        },
        .extended => {
            const extended = datas[inst].extended;
            switch (extended.opcode) {

                // Decl instructions are interesting but have no body.
                // TODO yes they do have a body actually. recurse over them just like block instructions.
                .struct_decl,
                .union_decl,
                .enum_decl,
                .opaque_decl,
                => return list.append(inst),

                else => return,
            }
        },

        // Block instructions, recurse over the bodies.

        .block, .block_comptime, .block_inline => {
            const inst_data = datas[inst].pl_node;
            const extra = zir.extraData(Inst.Block, inst_data.payload_index);
            const body = zir.extra[extra.end..][0..extra.data.body_len];
            return zir.findDeclsBody(list, body);
        },
        .condbr, .condbr_inline => {
            const inst_data = datas[inst].pl_node;
            const extra = zir.extraData(Inst.CondBr, inst_data.payload_index);
            const then_body = zir.extra[extra.end..][0..extra.data.then_body_len];
            const else_body = zir.extra[extra.end + then_body.len ..][0..extra.data.else_body_len];
            try zir.findDeclsBody(list, then_body);
            try zir.findDeclsBody(list, else_body);
        },
        .@"try", .try_ptr => {
            const inst_data = datas[inst].pl_node;
            const extra = zir.extraData(Inst.Try, inst_data.payload_index);
            const body = zir.extra[extra.end..][0..extra.data.body_len];
            try zir.findDeclsBody(list, body);
        },
        .switch_block => return findDeclsSwitch(zir, list, inst),

        .suspend_block => @panic("TODO iterate suspend block"),

        else => return, // Regular instruction, not interesting.
    }
}

fn findDeclsSwitch(
    zir: Zir,
    list: *std.ArrayList(Inst.Index),
    inst: Inst.Index,
) Allocator.Error!void {
    const inst_data = zir.instructions.items(.data)[inst].pl_node;
    const extra = zir.extraData(Inst.SwitchBlock, inst_data.payload_index);

    var extra_index: usize = extra.end;

    const multi_cases_len = if (extra.data.bits.has_multi_cases) blk: {
        const multi_cases_len = zir.extra[extra_index];
        extra_index += 1;
        break :blk multi_cases_len;
    } else 0;

    const special_prong = extra.data.bits.specialProng();
    if (special_prong != .none) {
        const body_len = @truncate(u31, zir.extra[extra_index]);
        extra_index += 1;
        const body = zir.extra[extra_index..][0..body_len];
        extra_index += body.len;

        try zir.findDeclsBody(list, body);
    }

    {
        const scalar_cases_len = extra.data.bits.scalar_cases_len;
        var scalar_i: usize = 0;
        while (scalar_i < scalar_cases_len) : (scalar_i += 1) {
            extra_index += 1;
            const body_len = @truncate(u31, zir.extra[extra_index]);
            extra_index += 1;
            const body = zir.extra[extra_index..][0..body_len];
            extra_index += body_len;

            try zir.findDeclsBody(list, body);
        }
    }
    {
        var multi_i: usize = 0;
        while (multi_i < multi_cases_len) : (multi_i += 1) {
            const items_len = zir.extra[extra_index];
            extra_index += 1;
            const ranges_len = zir.extra[extra_index];
            extra_index += 1;
            const body_len = @truncate(u31, zir.extra[extra_index]);
            extra_index += 1;
            const items = zir.refSlice(extra_index, items_len);
            extra_index += items_len;
            _ = items;

            var range_i: usize = 0;
            while (range_i < ranges_len) : (range_i += 1) {
                extra_index += 1;
                extra_index += 1;
            }

            const body = zir.extra[extra_index..][0..body_len];
            extra_index += body_len;

            try zir.findDeclsBody(list, body);
        }
    }
}

fn findDeclsBody(
    zir: Zir,
    list: *std.ArrayList(Inst.Index),
    body: []const Inst.Index,
) Allocator.Error!void {
    for (body) |member| {
        try zir.findDeclsInner(list, member);
    }
}

pub const FnInfo = struct {
    param_body: []const Inst.Index,
    param_body_inst: Inst.Index,
    ret_ty_body: []const Inst.Index,
    body: []const Inst.Index,
    ret_ty_ref: Zir.Inst.Ref,
    total_params_len: u32,
};

pub fn getParamBody(zir: Zir, fn_inst: Inst.Index) []const u32 {
    const tags = zir.instructions.items(.tags);
    const datas = zir.instructions.items(.data);
    const inst_data = datas[fn_inst].pl_node;

    const param_block_index = switch (tags[fn_inst]) {
        .func, .func_inferred => blk: {
            const extra = zir.extraData(Inst.Func, inst_data.payload_index);
            break :blk extra.data.param_block;
        },
        .func_fancy => blk: {
            const extra = zir.extraData(Inst.FuncFancy, inst_data.payload_index);
            break :blk extra.data.param_block;
        },
        else => unreachable,
    };

    const param_block = zir.extraData(Inst.Block, datas[param_block_index].pl_node.payload_index);
    return zir.extra[param_block.end..][0..param_block.data.body_len];
}

pub fn getFnInfo(zir: Zir, fn_inst: Inst.Index) FnInfo {
    const tags = zir.instructions.items(.tags);
    const datas = zir.instructions.items(.data);
    const info: struct {
        param_block: Inst.Index,
        body: []const Inst.Index,
        ret_ty_ref: Inst.Ref,
        ret_ty_body: []const Inst.Index,
    } = switch (tags[fn_inst]) {
        .func, .func_inferred => blk: {
            const inst_data = datas[fn_inst].pl_node;
            const extra = zir.extraData(Inst.Func, inst_data.payload_index);

            var extra_index: usize = extra.end;
            var ret_ty_ref: Inst.Ref = .none;
            var ret_ty_body: []const Inst.Index = &.{};

            switch (extra.data.ret_body_len) {
                0 => {
                    ret_ty_ref = .void_type;
                },
                1 => {
                    ret_ty_ref = @intToEnum(Inst.Ref, zir.extra[extra_index]);
                    extra_index += 1;
                },
                else => {
                    ret_ty_body = zir.extra[extra_index..][0..extra.data.ret_body_len];
                    extra_index += ret_ty_body.len;
                },
            }

            const body = zir.extra[extra_index..][0..extra.data.body_len];
            extra_index += body.len;

            break :blk .{
                .param_block = extra.data.param_block,
                .ret_ty_ref = ret_ty_ref,
                .ret_ty_body = ret_ty_body,
                .body = body,
            };
        },
        .func_fancy => blk: {
            const inst_data = datas[fn_inst].pl_node;
            const extra = zir.extraData(Inst.FuncFancy, inst_data.payload_index);

            var extra_index: usize = extra.end;
            var ret_ty_ref: Inst.Ref = .void_type;
            var ret_ty_body: []const Inst.Index = &.{};

            extra_index += @boolToInt(extra.data.bits.has_lib_name);
            if (extra.data.bits.has_align_body) {
                extra_index += zir.extra[extra_index] + 1;
            } else if (extra.data.bits.has_align_ref) {
                extra_index += 1;
            }
            if (extra.data.bits.has_addrspace_body) {
                extra_index += zir.extra[extra_index] + 1;
            } else if (extra.data.bits.has_addrspace_ref) {
                extra_index += 1;
            }
            if (extra.data.bits.has_section_body) {
                extra_index += zir.extra[extra_index] + 1;
            } else if (extra.data.bits.has_section_ref) {
                extra_index += 1;
            }
            if (extra.data.bits.has_cc_body) {
                extra_index += zir.extra[extra_index] + 1;
            } else if (extra.data.bits.has_cc_ref) {
                extra_index += 1;
            }
            if (extra.data.bits.has_ret_ty_body) {
                const body_len = zir.extra[extra_index];
                extra_index += 1;
                ret_ty_body = zir.extra[extra_index..][0..body_len];
                extra_index += ret_ty_body.len;
            } else if (extra.data.bits.has_ret_ty_ref) {
                ret_ty_ref = @intToEnum(Inst.Ref, zir.extra[extra_index]);
                extra_index += 1;
            }

            extra_index += @boolToInt(extra.data.bits.has_any_noalias);

            const body = zir.extra[extra_index..][0..extra.data.body_len];
            extra_index += body.len;
            break :blk .{
                .param_block = extra.data.param_block,
                .ret_ty_ref = ret_ty_ref,
                .ret_ty_body = ret_ty_body,
                .body = body,
            };
        },
        else => unreachable,
    };
    assert(tags[info.param_block] == .block or
        tags[info.param_block] == .block_comptime or
        tags[info.param_block] == .block_inline);
    const param_block = zir.extraData(Inst.Block, datas[info.param_block].pl_node.payload_index);
    const param_body = zir.extra[param_block.end..][0..param_block.data.body_len];
    var total_params_len: u32 = 0;
    for (param_body) |inst| {
        switch (tags[inst]) {
            .param, .param_comptime, .param_anytype, .param_anytype_comptime => {
                total_params_len += 1;
            },
            else => continue,
        }
    }
    return .{
        .param_body = param_body,
        .param_body_inst = info.param_block,
        .ret_ty_body = info.ret_ty_body,
        .ret_ty_ref = info.ret_ty_ref,
        .body = info.body,
        .total_params_len = total_params_len,
    };
}

const ref_start_index: u32 = Inst.Ref.typed_value_map.len;

pub fn indexToRef(inst: Inst.Index) Inst.Ref {
    return @intToEnum(Inst.Ref, ref_start_index + inst);
}

pub fn refToIndex(inst: Inst.Ref) ?Inst.Index {
    const ref_int = @enumToInt(inst);
    if (ref_int >= ref_start_index) {
        return ref_int - ref_start_index;
    } else {
        return null;
    }
}
