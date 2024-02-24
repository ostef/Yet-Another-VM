RegistersState :: struct
{
    instruction_pointer : *u8;
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
    Mul;
    Div;

    Push_Const;
    Pop;
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

ExecuteAdd :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a + b);
ExecuteSub :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a - b);
ExecuteMul :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a * b);
ExecuteDiv :: #bake_arguments BinopHelperForAllTypes (func = (a, b) => a / b);

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

ExecuteNextInstruction :: inline (using vm : *VirtualMachine) -> ExecuteStatus
{
    opcode := ReadInstructionOpCode (vm);
    if #complete opcode ==
    {
    case .No_Op;
    case .Halt;
        return .Program_Halted;
    case .Add;
        return ExecuteAdd (vm);
    case .Sub;
        return ExecuteSub (vm);
    case .Mul;
        return ExecuteMul (vm);
    case .Div;
        return ExecuteDiv (vm);
    case .Push_Const;
        return ExecutePushConst (vm);
    case .Pop;
        return ExecutePop (vm);
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
