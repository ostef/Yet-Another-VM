#import "Lexer";

// We prevent errors by #complete switching on each value of OpCode
// instead of having to manually keep track of an implicit order
Asm_Mnemonics :: #run -> [OpCode_Count]string
{
    Get :: (opcode : OpCode) -> string #must
    {
        if #complete opcode ==
        {
        case .Halt; return "halt";
        case .No_Op; return "noop";

        case .Add; return "add";
        case .Sub; return "sub";
        case .Neg; return "neg";
        case .Mul; return "mul";
        case .Div; return "div";

        case .And; return "and";
        case .Or; return "or";
        case .Xor; return "xor";
        case .Not; return "not";

        case .Comp_Eq; return "compeq";
        case .Comp_Ne; return "compne";
        case .Comp_Lt; return "complt";
        case .Comp_Le; return "comple";
        case .Comp_Gt; return "compgt";
        case .Comp_Ge; return "compge";

        case .Local_Var; return "local_var";
        case .Push_Const; return "push_const";
        case .Push_Local; return "push_local";
        case .Pop; return "pop";
        case .Pop_Local; return "pop_local";
        case .Swap; return "swap";

        case .Cast; return "cast";
        }
    }

    result : [OpCode_Count]string;

    for type_info (OpCode).values
        result[it_index] = Get (cast (OpCode) it);

    return result;
};

#assert Asm_Mnemonics.count == OpCode_Count;

Asm_Type_Names :: string.[
    "void",
    "u8",
    "s8",
    "u16",
    "s16",
    "u32",
    "s32",
    "u64",
    "s64",
    "f32",
    "f64",
];

#assert Asm_Type_Names.count == type_info (ValueType).values.count;

AsmParser :: struct
{
    #as using lexer : Lexer;
}

SkipWhitespacesAndComments :: inline (using lexer : *Lexer)
{
    while !LexerIsAtEnd (lexer)
    {
        if Basic.is_space (text[byte_index])
        {
            LexerAdvance (lexer);
        }
        else if LexerMatchString (lexer, ";")
        {
            LexerAdvanceUntilMatches (lexer, "\n");
        }
        else
        {
            break;
        }
    }
}

ParseType :: (parser : *AsmParser) -> ValueType #must, bool #must
{
    SkipWhitespacesAndComments (parser);

    for Asm_Type_Names
    {
        if LexerMatchAlphaNumeric (parser, it)
        {
            return cast (ValueType) it_index, true;
        }
    }

    SyntaxError (parser, "Expected a type but got this:\n%", LexerGetLine (parser));

    return .Void, false;
}

ParseConstantValue :: (parser : *AsmParser, bytes : *[..]u8, type : ValueType) -> bool
{
    SkipWhitespacesAndComments (parser);

    if #complete type ==
    {
    case .Void;
        return false;

    case .U8; #through;
    case .S8; #through;
    case .U16; #through;
    case .S16; #through;
    case .U32; #through;
    case .S32; #through;
    case .U64; #through;
    case .S64;

        str := LexerRemainingBytesString (parser);
        value, ok, remainder := Basic.string_to_int (str);
        if !ok
        {
            SyntaxError (parser, "Expected an integer value of type %:\n%",
                Asm_Type_Names[type], LexerGetLine (parser));

            return false;
        }

        LexerAdvance (parser, cast (s64) (remainder.data - str.data));

        for i : 0..Value_Type_Size[type] - 1
        {
            ArrayPush (bytes, cast (u8) (value & 0xff));
            value >>= 8;
        }

    case .F32;
        str := LexerRemainingBytesString (parser);
        float_value, ok, remainder := Basic.string_to_float (str);
        if !ok
        {
            SyntaxError (parser, "Expected a floating point value of type %:\n%",
                Asm_Type_Names[type], LexerGetLine (parser));

            return false;
        }

        LexerAdvance (parser, cast (s64) (remainder.data - str.data));

        value : u32 = (cast (*u32) (*float_value)).*;
        ArrayPush (bytes, cast (u8) ((value >>  0) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >>  8) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 16) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 24) & 0xff));

    case .F64;
        str := LexerRemainingBytesString (parser);
        float_value, ok, remainder := Basic.string_to_float64 (str);
        if !ok
        {
            SyntaxError (parser, "Expected a floating point value of type %:\n%",
                Asm_Type_Names[type], LexerGetLine (parser));

            return false;
        }

        LexerAdvance (parser, cast (s64) (remainder.data - str.data));

        value : u64 = (cast (*u64) (*float_value)).*;
        ArrayPush (bytes, cast (u8) ((value >>  0) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >>  8) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 16) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 24) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 32) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 40) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 48) & 0xff));
        ArrayPush (bytes, cast (u8) ((value >> 56) & 0xff));
    }

    return true;
}

ParseInstruction :: (parser : *AsmParser, bytes : *[..]u8, opcode : OpCode) -> bool
{
    SkipWhitespacesAndComments (parser);

    if #complete opcode ==
    {
    case .No_Op; #through;
    case .Halt;
        return true;

    case .Add; #through;
    case .Sub; #through;
    case .Neg; #through;
    case .Mul; #through;
    case .Div; #through;
    case .And; #through;
    case .Or; #through;
    case .Xor; #through;
    case .Not; #through;
    case .Comp_Eq; #through;
    case .Comp_Ne; #through;
    case .Comp_Lt; #through;
    case .Comp_Le; #through;
    case .Comp_Gt; #through;
    case .Comp_Ge; #through;
    case .Pop;
        type, ok := ParseType (parser);
        if !ok
            return false;

        invalid_type := type == .Void;
        invalid_type |= opcode == .Neg
            && (type == .U8 || type == .U16 || type == .U32 || type == .U64);
        invalid_type |= (opcode == .And || opcode == .Or || opcode == .Xor || opcode == .Not)
            && (type == .F32 || type == .F64);

        if invalid_type
        {
            SyntaxError (parser, "Invalid type % for % instruction:\n%",
                Asm_Type_Names[type], Asm_Mnemonics[opcode], LexerGetLine (parser));

            return false;
        }

        ArrayPush (bytes, cast (u8) type);

        return true;

    case .Local_Var; #through;
    case .Push_Const;
        type, ok := ParseType (parser);
        if !ok
            return false;

        if type == .Void
        {
            SyntaxError (parser, "Invalid type % for % instruction:\n%",
                Asm_Type_Names[type], Asm_Mnemonics[opcode], LexerGetLine (parser));

            return false;
        }

        ArrayPush (bytes, cast (u8) type);

        return ParseConstantValue (parser, bytes, type);

    case .Push_Local; #through;
    case .Pop_Local;
        type, ok := ParseType (parser);
        if !ok
            return false;

        if type == .Void
        {
            SyntaxError (parser, "Invalid type % for % instruction:\n%",
                Asm_Type_Names[type], Asm_Mnemonics[opcode], LexerGetLine (parser));

            return false;
        }

        ArrayPush (bytes, cast (u8) type);

        return ParseConstantValue (parser, bytes, .U32);

    case .Swap; #through;
    case .Cast;
        from_type, ok := ParseType (parser);
        if !ok
            return false;

        if from_type == .Void
        {
            SyntaxError (parser, "Invalid type % for % instruction:\n%",
                Asm_Type_Names[from_type], Asm_Mnemonics[opcode], LexerGetLine (parser));

            return false;
        }

        to_type:, ok = ParseType (parser);
        if !ok
            return false;

        if to_type == .Void
        {
            SyntaxError (parser, "Invalid type % for % instruction:\n%",
                Asm_Type_Names[to_type], Asm_Mnemonics[opcode], LexerGetLine (parser));

            return false;
        }

        ArrayPush (bytes, cast (u8) from_type);
        ArrayPush (bytes, cast (u8) to_type);

        return true;
    }
}

ParseAssemblyFile :: (filename : string, file_contents : string) -> []u8 #must, bool
{
    bytes : [..]u8;

    parser : AsmParser;
    parser.name = filename;
    parser.text = file_contents;

    SkipWhitespacesAndComments (*parser);

    while !LexerIsAtEnd (*parser)
    {
        opcode : u8 = 0xff;

        for Asm_Mnemonics
        {
            if LexerMatchAlphaNumeric (*parser, it)
            {
                opcode = xx it_index;
                break;
            }
        }

        if opcode == 0xff
        {
            SyntaxError (*parser, "Invalid instruction mnemonic:\n%", LexerGetLine (parser));
            return bytes, false;
        }

        ArrayPush (*bytes, opcode);

        if !ParseInstruction (*parser, *bytes, cast (OpCode) opcode)
            return bytes, false;

        SkipWhitespacesAndComments (*parser);
    }

    return bytes, true;
}

Disassemble :: (builder : *StringBuilder, bytes : []u8) -> bool
{
    cursor := 0;
    while cursor < bytes.count
    {
        opcode := bytes[cursor];
        cursor += 1;

        if opcode >= Asm_Mnemonics.count
            return false;

        StringBuilderAppend (builder, Asm_Mnemonics[opcode]);

        if #complete cast (OpCode) opcode ==
        {
        case .No_Op;
        case .Halt;
        case .Add; #through;
        case .Sub; #through;
        case .Neg; #through;
        case .Mul; #through;
        case .Div; #through;
        case .And; #through;
        case .Or; #through;
        case .Xor; #through;
        case .Not; #through;
        case .Comp_Eq; #through;
        case .Comp_Ne; #through;
        case .Comp_Lt; #through;
        case .Comp_Le; #through;
        case .Comp_Gt; #through;
        case .Comp_Ge; #through;
        case .Pop;
            if cursor >= bytes.count
                return false;

            type := bytes[cursor];
            cursor += 1;
            if type >= Asm_Type_Names.count
                return false;

            StringBuilderAppend (builder, " %", Asm_Type_Names[type]);

        case .Local_Var; #through;
        case .Push_Const;
            if cursor >= bytes.count
                return false;

            type := bytes[cursor];
            cursor += 1;
            if type >= Asm_Type_Names.count
                return false;

            if cursor + Value_Type_Size[type] > bytes.count
                return false;

            if #complete cast (ValueType) type ==
            {
            case .Void;
                StringBuilderAppend (builder, " %", Asm_Type_Names[type]);
            case .U8;
                value := (cast (*u8) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .S8;
                value := (cast (*s8) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .U16;
                value := (cast (*u16) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .S16;
                value := (cast (*s16) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .U32;
                value := (cast (*u32) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .S32;
                value := (cast (*s32) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .U64;
                value := (cast (*u64) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .S64;
                value := (cast (*s64) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .F32;
                value := (cast (*float32) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            case .F64;
                value := (cast (*float64) *bytes[cursor]).*;
                StringBuilderAppend (builder, " % %", Asm_Type_Names[type], value);
            }

            cursor += Value_Type_Size[type];

        case .Push_Local; #through;
        case .Pop_Local;
            if cursor >= bytes.count
                return false;

            type := bytes[cursor];
            cursor += 1;
            if type >= Asm_Type_Names.count
                return false;

            if cursor + size_of (u32) > bytes.count
                return false;

            stack_offset := (cast (*u32) *bytes[cursor]).*;
            cursor += size_of (u32);

            StringBuilderAppend (builder, " % %", Asm_Type_Names[type], stack_offset);

        case .Swap; #through;
        case .Cast;
            if cursor >= bytes.count
                return false;

            from_type := bytes[cursor];
            cursor += 1;
            if from_type >= Asm_Type_Names.count
                return false;

            if cursor >= bytes.count
                return false;

            to_type := bytes[cursor];
            cursor += 1;
            if to_type >= Asm_Type_Names.count
                return false;

            StringBuilderAppend (builder, " % %", Asm_Type_Names[from_type], Asm_Type_Names[to_type]);
        }

        StringBuilderAppend (builder, "\n");
    }

    return true;
}

Disassemble :: inline (bytes : []u8) -> bool
{
    builder : StringBuilder;
    if !Disassemble (*builder, bytes)
        return false;

    Println (StringBuilderBuild (*builder));

    return true;
}
