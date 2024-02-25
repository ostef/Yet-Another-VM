#import "Common";

Basic :: #import "Basic";
#import "File";

#load "assembler.jai";
#load "vm.jai";

main :: ()
{
    context.allocator = Temp;

    command_line_args := Basic.get_command_line_arguments ();
    if command_line_args.count == 1
    {
        Println ("Error: No file provided");
        Basic.exit (1);
    }

    filename := command_line_args[1];
    file_contents, ok := read_entire_file (filename, log_errors = false);
    if !ok
    {
        Println ("Error: Could not read file '%'", filename);
        Basic.exit (1);
    }

    bytes:, ok = ParseAssemblyFile (filename, file_contents);
    if !ok
    {
        Println ("Error: Could not parse file '%'", filename);
        Basic.exit (1);
    }

    if !Disassemble (bytes)
    {
        Println ("Error: Could not disassemble file");
        Basic.exit (1);
    }

    stack : [1024]u8 = ---;
    vm : VirtualMachine;
    vm.instruction_pointer = bytes.data;
    vm.stack_base = stack.data;
    vm.stack_pointer = stack.data;

    status := Execute (*vm);

    if #complete status ==
    {
    case .Ok; Println ("Ok");
    case .Program_Halted; Println ("Program halted");
    case .Invalid_OpCode; Println ("Invalid opcode");
    case .Invalid_Instruction; Println ("Invalid instruction");
    case .Invalid_Type_Operand; Println ("Invalid type operand");
    }
}

#run
{
    JaiC :: #import "Compiler";

    JaiC.set_build_options_dc (.{output_executable_name="yavm", output_path="../"});
}
