RegistersState :: struct
{
    instruction_pointer : *u8;
    stack_base : *u8;
    stack_pointer : *u8;
}

VirtualMachine :: struct
{
    #as using registers_state : RegistersState;
    memory : []u8;
}

OpCode :: enum u8
{
    Halt;
    No_Op;

    Add;
    Sub;
    Neg;
    Mul;
    Div;

    And;
    Or;
    Xor;
    Not;

    Local_Var;
    Push_Const;
    Push_Local;
    Pop;
    Pop_Local;
}

OpCode_Count :: #run type_info (OpCode).values.count;

ValueType :: enum u8
{
    Void;
    U8;
    S8;
    U16;
    S16;
    U32;
    S32;
    U64;
    S64;
    F32;
    F64;
}

Value_Type_Size :: s64.[
    0,
    1,1,
    2,2,
    4,4,
    8,8,
    4,4,
    8,8,
];

ReadInstructionOpCode :: #bake_arguments ReadInstructionOperand (T = OpCode);

ReadInstructionOperand :: inline (using vm : *VirtualMachine, $T : Type) -> T #must
{
    value := (cast (*T) instruction_pointer).*;
    instruction_pointer += size_of (T);

    return value;
}

ExecuteStatus :: enum
{
    Ok;
    Program_Halted;

    Invalid_OpCode;
    Invalid_Instruction;
    Invalid_Type_Operand;
}

ExecuteResult :: struct
{
    registers_state : RegistersState;
    status : ExecuteStatus;
}

Push :: inline (using vm : *VirtualMachine, $T : Type) -> *T #must
{
    result := cast (*T) stack_pointer;
    stack_pointer += size_of (T);

    return result;
}

Push :: inline (using vm : *VirtualMachine, $T : Type, value : T)
{
    Println ("Push -- % %", T, value);
    (cast (*T) stack_pointer).* = value;
    stack_pointer += size_of (T);
}

Pop :: inline (using vm : *VirtualMachine, $T : Type) -> T
{
    stack_pointer -= size_of (T);

    value := (cast (*T) stack_pointer).*;
    Println ("Pop  -- % %", T, value);

    return value;
}

BinopHelper :: ($T : Type) #expand
{
    a := Pop (`vm, T);
    b := Pop (`vm, T);
    Push (`vm, T, `f (a, b));
}

BinopHelperForAllTypes :: (using vm : *VirtualMachine, $func : (a : $T, b : T) -> T) -> ExecuteStatus
{
    type := ReadInstructionOperand (vm, ValueType);

    f :: func;
    if #complete type ==
    {
    case .Void;
       return .Invalid_Type_Operand;
    case .U8;
        BinopHelper (u8);
    case .S8;
        BinopHelper (s8);
    case .U16;
        BinopHelper (u16);
    case .S16;
        BinopHelper (s16);
    case .U32;
        BinopHelper (u32);
    case .S32;
        BinopHelper (s32);
    case .U64;
        BinopHelper (u64);
    case .S64;
        BinopHelper (s64);
    case .F32;
        BinopHelper (float32);
    case .F64;
        BinopHelper (float64);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

BinopHelperForIntegerTypes :: (using vm : *VirtualMachine, $func : (a : $T, b : T) -> T) -> ExecuteStatus
{
    type := ReadInstructionOperand (vm, ValueType);

    f :: func;
    if #complete type ==
    {
    case .Void; #through;
    case .F32; #through;
    case .F64;
       return .Invalid_Type_Operand;
    case .U8;
        BinopHelper (u8);
    case .S8;
        BinopHelper (s8);
    case .U16;
        BinopHelper (u16);
    case .S16;
        BinopHelper (s16);
    case .U32;
        BinopHelper (u32);
    case .S32;
        BinopHelper (s32);
    case .U64;
        BinopHelper (u64);
    case .S64;
        BinopHelper (s64);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

ExecuteAdd :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a + b);
ExecuteSub :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a - b);

ExecuteNeg :: (using vm : *VirtualMachine) -> ExecuteStatus
{
    Helper :: ($T : Type) #expand
    {
        v := Pop (`vm, T);
        Push (`vm, T, -v);
    }

    type := ReadInstructionOperand (vm, ValueType);

    if #complete type ==
    {
    case .Void; #through;
    case .U8; #through;
    case .U16; #through;
    case .U32; #through;
    case .U64;
       return .Invalid_Type_Operand;
    case .S8;
        Helper (s8);
    case .S16;
        Helper (s16);
    case .S32;
        Helper (s32);
    case .S64;
        Helper (s64);
    case .F32;
        Helper (float32);
    case .F64;
        Helper (float64);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

ExecuteMul :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a * b);
ExecuteDiv :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a / b);

ExecuteAnd :: #bake_arguments BinopHelperForIntegerTypes (func = (a, b) => a & b);
ExecuteOr :: #bake_arguments BinopHelperForIntegerTypes (func = (a, b) => a | b);
ExecuteXor :: #bake_arguments BinopHelperForIntegerTypes (func = (a, b) => a ^ b);

ExecuteNot :: (using vm : *VirtualMachine) -> ExecuteStatus
{
    Helper :: ($T : Type) #expand
    {
        v := Pop (`vm, T);
        Push (`vm, T, v);
    }

    type := ReadInstructionOperand (vm, ValueType);

    if #complete type ==
    {
    case .Void; #through;
    case .F32; #through;
    case .F64;
       return .Invalid_Type_Operand;
    case .U8;
        v := Pop (vm, u8);
        Push (vm, u8, v ^ 0xff);
    case .S8;
        v := Pop (vm, s8);
        Push (vm, s8, v ^ 0xff);
    case .U16;
        v := Pop (vm, u16);
        Push (vm, u16, v ^ 0xffff);
    case .S16;
        v := Pop (vm, s16);
        Push (vm, s16, v ^ 0xffff);
    case .U32;
        v := Pop (vm, u32);
        Push (vm, u32, v ^ 0xffffffff);
    case .S32;
        v := Pop (vm, s32);
        Push (vm, s32, v ^ 0xffffffff);
    case .U64;
        v := Pop (vm, u64);
        Push (vm, u64, v ^ 0xffffffffffffffff);
    case .S64;
        v := Pop (vm, s64);
        Push (vm, s64, v ^ 0xffffffffffffffff);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

ExecuteLocalVar :: ExecutePushConst;

ExecutePushConst :: inline (using vm : *VirtualMachine) -> ExecuteStatus
{
    type := ReadInstructionOperand (vm, ValueType);
    if #complete type ==
    {
    case .Void;
        return .Invalid_Type_Operand;
    case .U8;
        value := ReadInstructionOperand (vm, u8);
        Push (vm, u8, value);
    case .S8;
        value := ReadInstructionOperand (vm, s8);
        Push (vm, s8, value);
    case .U16;
        value := ReadInstructionOperand (vm, u16);
        Push (vm, u16, value);
    case .S16;
        value := ReadInstructionOperand (vm, s16);
        Push (vm, s16, value);
    case .U32;
        value := ReadInstructionOperand (vm, u32);
        Push (vm, u32, value);
    case .S32;
        value := ReadInstructionOperand (vm, s32);
        Push (vm, s32, value);
    case .U64;
        value := ReadInstructionOperand (vm, u64);
        Push (vm, u64, value);
    case .S64;
        value := ReadInstructionOperand (vm, s64);
        Push (vm, s64, value);
    case .F32;
        value := ReadInstructionOperand (vm, float32);
        Push (vm, float32, value);
    case .F64;
        value := ReadInstructionOperand (vm, float64);
        Push (vm, float64, value);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

ExecutePushLocal :: inline (using vm : *VirtualMachine) -> ExecuteStatus
{
    type := ReadInstructionOperand (vm, ValueType);
    stack_offset := ReadInstructionOperand (vm, u32);
    ptr := stack_base + stack_offset;

    if #complete type ==
    {
    case .Void;
        return .Invalid_Type_Operand;
    case .U8;
        Push (vm, u8, (cast (*u8) ptr).*);
    case .S8;
        Push (vm, s8, (cast (*s8) ptr).*);
    case .U16;
        Push (vm, u16, (cast (*u16) ptr).*);
    case .S16;
        Push (vm, s16, (cast (*s16) ptr).*);
    case .U32;
        Push (vm, u32, (cast (*u32) ptr).*);
    case .S32;
        Push (vm, s32, (cast (*s32) ptr).*);
    case .U64;
        Push (vm, u64, (cast (*u64) ptr).*);
    case .S64;
        Push (vm, s64, (cast (*s64) ptr).*);
    case .F32;
        Push (vm, float32, (cast (*float32) ptr).*);
    case .F64;
        Push (vm, float64, (cast (*float64) ptr).*);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

ExecutePop :: inline (using vm : *VirtualMachine) -> ExecuteStatus
{
    type := ReadInstructionOperand (vm, ValueType);
    if #complete type ==
    {
    case .Void;
        return .Invalid_Type_Operand;
    case .U8;
        Pop (vm, u8);
    case .S8;
        Pop (vm, s8);
    case .U16;
        Pop (vm, u16);
    case .S16;
        Pop (vm, s16);
    case .U32;
        Pop (vm, u32);
    case .S32;
        Pop (vm, s32);
    case .U64;
        Pop (vm, u64);
    case .S64;
        Pop (vm, s64);
    case .F32;
        Pop (vm, float32);
    case .F64;
        Pop (vm, float64);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

ExecutePopLocal :: inline (using vm : *VirtualMachine) -> ExecuteStatus
{
    type := ReadInstructionOperand (vm, ValueType);
    stack_offset := ReadInstructionOperand (vm, u32);
    ptr := stack_base + stack_offset;

    if #complete type ==
    {
    case .Void;
        return .Invalid_Type_Operand;
    case .U8;
        (cast (*u8) ptr).* = Pop (vm, u8);
    case .S8;
        (cast (*s8) ptr).* = Pop (vm, s8);
    case .U16;
        (cast (*u16) ptr).* = Pop (vm, u16);
    case .S16;
        (cast (*s16) ptr).* = Pop (vm, s16);
    case .U32;
        (cast (*u32) ptr).* = Pop (vm, u32);
    case .S32;
        (cast (*s32) ptr).* = Pop (vm, s32);
    case .U64;
        (cast (*u64) ptr).* = Pop (vm, u64);
    case .S64;
        (cast (*s64) ptr).* = Pop (vm, s64);
    case .F32;
        (cast (*float32) ptr).* = Pop (vm, float32);
    case .F64;
        (cast (*float64) ptr).* = Pop (vm, float64);
    case;
        return .Invalid_Instruction;
    }

    return .Ok;
}

ExecuteNextInstruction :: inline (using vm : *VirtualMachine) -> ExecuteStatus
{
    opcode := ReadInstructionOpCode (vm);
    if #complete opcode ==
    {
    case .No_Op;
        return .Ok;
    case .Halt;
        return .Program_Halted;
    case .Add;
        return ExecuteAdd (vm);
    case .Sub;
        return ExecuteSub (vm);
    case .Neg;
        return ExecuteNeg (vm);
    case .Mul;
        return ExecuteMul (vm);
    case .Div;
        return ExecuteDiv (vm);
    case .And;
        return ExecuteAnd (vm);
    case .Or;
        return ExecuteOr (vm);
    case .Xor;
        return ExecuteXor (vm);
    case .Not;
        return ExecuteNot (vm);
    case .Local_Var;
        return ExecuteLocalVar (vm);
    case .Push_Const;
        return ExecutePushConst (vm);
    case .Push_Local;
        return ExecutePushLocal (vm);
    case .Pop;
        return ExecutePop (vm);
    case .Pop_Local;
        return ExecutePopLocal (vm);
    }

    return .Invalid_OpCode;
}

Execute :: (using vm : *VirtualMachine) -> ExecuteStatus
{
    status : ExecuteStatus;
    while status == .Ok
    {
        status = ExecuteNextInstruction (vm);
    }

    return status;
}
