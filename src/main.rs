mod analyze;
mod vm;
mod compiler;
mod video;

use anyhow::*;

fn main() -> Result<()> {
    env_logger::builder()
        .filter(None, log::LevelFilter::max())
        .init();
    let mut pargs = pico_args::Arguments::from_env();
    if let Some(cmd) = pargs.subcommand().expect("failed to parse arguments") {
        match cmd.as_ref() {
            "analyze" => {
                analyze::analyze();
            },
            "frequencies" => {
                analyze::frequencies();
            },
            "video" => {
                video::video();
            },
            "vm" => {
                let mut st = vm::State::new();
                let mut prog = vm::Program::new(vec![
                    vm::Instruction::GlobalAddr,
                    vm::Instruction::Lit64(1337),
                    vm::Instruction::Add,
                    vm::Instruction::Lit16(0),
                    vm::Instruction::Write,

                    vm::Instruction::Here,
                    vm::Instruction::GlobalAddr,
                    vm::Instruction::Lit64(1337),
                    vm::Instruction::Add,
                    vm::Instruction::Dup,
                    vm::Instruction::Read16,
                    vm::Instruction::Dup,
                    vm::Instruction::Dump,
                    vm::Instruction::Lit8(1),
                    vm::Instruction::Add,
                    vm::Instruction::Write,
                    vm::Instruction::Jump,
                ]);
                prog.run(&mut st);
            },
            "compile" => {
                let path: String = pargs.free_from_str().expect("specify a path to compile");
                let config = lang_c::driver::Config::default();
                let t = lang_c::driver::parse(&config, &path).unwrap();
                log::info!("{:?}", t);
                let mut comp = compiler::State::new();
                comp.load(&path);
                let (entry, ins) = comp.finalize();
                log::info!("{:#?}", ins);
                let mut vm = vm::State::new();
                let mut prog = vm::Program::new(ins);
                prog.pc = entry;
                prog.run(&mut vm);
            },
            _ => {},
        }
    }
    Ok(())
}
