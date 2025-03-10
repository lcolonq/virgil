mod analyze;
mod vm;
mod compiler;

use teleia::*;
use clap::{arg, command, Command};

#[tokio::main]
pub async fn main() -> Erm<()> {
    let matches = command!()
        .propagate_version(true)
        .subcommand_required(true)
        .arg_required_else_help(true)
        .subcommand(
            Command::new("analyze")
                .about("Analyze the Bad Apple!! video to produce frame data JSON")
        )
        .subcommand(
            Command::new("frequencies")
                .about("Output information about the relative frequencies of each pixel region")
        )
        .subcommand(
            Command::new("vm")
                .about("Run the Bad Apple!! virtual machine")
        )
        .subcommand(
            Command::new("compile")
                .about("Compile C source targeting the Bad Apple!! virtual machine")
                .arg(arg!(<path> "Path to source file"))
        )
        .get_matches();
    match matches.subcommand() {
        Some(("analyze", _cm)) => {
            analyze::analyze();
        },
        Some(("frequencies", _cm)) => {
            analyze::frequencies();
        },
        Some(("vm", _cm)) => {
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
        Some(("compile", cm)) => {
            env_logger::Builder::new()
                .filter(None, log::LevelFilter::Info)
                .init();
            install_error_handler();
            let path = cm.get_one::<String>("path").unwrap();
            let mut comp = compiler::State::new();
            comp.load(&path)?;
            let (entry, ins) = comp.finalize()?;
            let mut vm = vm::State::new();
            let mut prog = vm::Program::new(ins);
            prog.pc = entry;
            prog.run(&mut vm);
        },
        _ => {},
    }
    Ok(())
}
