mod analyze;
mod vm;

fn main() {
    let mut pargs = pico_args::Arguments::from_env();
    if let Some(cmd) = pargs.subcommand().expect("failed to parse arguments") {
        match cmd.as_ref() {
            "analyze" => {
                analyze::analyze();
            },
            "frequencies" => {
                analyze::frequencies();
            },
            "vm" => {
                let mut st = vm::State::new();
                st.run_instruction(&vm::Instruction::GlobalAddr);
                st.run_instruction(&vm::Instruction::Lit64(1337));
                st.run_instruction(&vm::Instruction::Add);
                st.run_instruction(&vm::Instruction::Lit32(0xdeadbeef));
                st.run_instruction(&vm::Instruction::Write);
                st.run_instruction(&vm::Instruction::GlobalAddr);
                st.run_instruction(&vm::Instruction::Lit64(1337));
                st.run_instruction(&vm::Instruction::Add);
                st.run_instruction(&vm::Instruction::Read32);
                println!("{:?}", st.stack);
                println!("{:?}", st.globals);
            },
            _ => {},
        }
    }
}
