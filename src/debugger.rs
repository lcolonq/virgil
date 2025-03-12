use std::{io::{BufRead, BufReader, Read}, sync::mpsc::{channel, Receiver, RecvError, Sender, TryRecvError}};
use std::io::Write;
use serde::{Deserialize, Serialize};

use teleia::*;

use crate::{compiler, vm};

#[derive(Debug, Deserialize)]
#[serde(tag = "cmd", content = "args")]
pub enum Command {
    Step,
    StepStatement,
    Break(u64),
    BreakStatement(u64),
    Stop,
    Continue,
}

#[derive(Serialize)]
pub struct SourceInfo {
    pub function: Option<String>,
    pub stmt: Option<(u64, u64)>,
}

#[derive(Serialize)]
#[serde(tag = "cmd", content = "args")]
pub enum Response<'a> {
    StateUpdate(u64, &'a vm::State, SourceInfo),
    Program(&'a vm::Program),
    Source(&'a str),

}

pub enum Mode {
    Paused,
    Running,
}

pub struct Debugger {
    mode: Mode,
    vm: vm::State,
    prog: vm::Program,
    src: Option<String>,
    debug: compiler::debug::Info,
    breakpoints: Vec<u64>,
}
impl Debugger {
    pub fn new(entry: u64, ins: Vec<vm::Instruction>, debug: compiler::debug::Info, src: Option<String>) -> Self {
        let mut prog = vm::Program::new(ins);
        prog.pc = entry;
        Self {
            mode: Mode::Paused,
            vm: vm::State::new(),
            prog,
            src,
            debug,
            breakpoints: Vec::new(),
        }
    }
    fn send<X>(&self, x: X) -> Erm<()> where X: Serialize {
        let mut stdout = std::io::stdout();
        serde_json::to_writer(&mut stdout, &x)?;
        write!(&mut stdout, "\n")?;
        stdout.flush()?;
        Ok(())
    }
    pub fn send_state_update(&self) -> Erm<()> {
        let mfunc = self.debug.functions.iter()
            .find(|f| f.instructions.contains(&self.prog.pc));
        let mstmt = mfunc.and_then(|func| {
            func.statements.iter()
                .find(|s| s.instructions.contains(&self.prog.pc))
        });
        let srcinfo = SourceInfo {
            function: mfunc.map(|f| f.nm.clone()),
            stmt: mstmt.map(|s| (s.src_start, s.src_end)),
        };
        self.send(Response::StateUpdate(self.prog.pc, &self.vm, srcinfo))
    }
    pub fn send_program(&self) -> Erm<()> {
        self.send(Response::Program(&self.prog))
    }
    pub fn send_source(&self) -> Erm<()> {
        if let Some(src) = &self.src {
            self.send(Response::Source(&src))?;
        }
        Ok(())
    }
    pub fn cmd(&mut self, cmd: Command) -> Erm<()> {
        match cmd {
            Command::Step => {
                self.prog.step(&mut self.vm)?;
            },
            Command::StepStatement => todo!(),
            Command::Break(bp) => {
                if !self.breakpoints.contains(&bp) {
                    self.breakpoints.push(bp);
                }
            },
            Command::BreakStatement(_) => todo!(),
            Command::Stop => { self.mode = Mode::Paused; },
            Command::Continue => { self.mode = Mode::Running; },
        }
        Ok(())
    }
    pub fn run(&mut self, cmds: Receiver<Command>) -> Erm<()> {
        self.send_program()?;
        self.send_source()?;
        loop {
            match self.mode {
                Mode::Paused => {
                    match cmds.recv() {
                        Ok(cmd) => {
                            self.cmd(cmd)?;
                            self.send_state_update()?;
                        },
                        Err(RecvError) => break,
                    }
                },
                Mode::Running => {
                    self.prog.step(&mut self.vm)?;
                    match cmds.try_recv() {
                        Ok(cmd) => self.cmd(cmd)?,
                        Err(TryRecvError::Empty) => break,
                        Err(TryRecvError::Disconnected) => {},
                    }
                },
            }
        }
        Ok(())
    }
}

pub struct Interpreter {
    pub sender: Sender<Command>,
}
impl Interpreter {
    pub fn new() -> (Self, Receiver<Command>) {
        let (sender, receiver) = channel();
        ( Self {
            sender,
        }, receiver
        )
    }
    pub fn run<R>(&mut self, inp: R) -> Erm<()> where R: Read {
        let mut reader = BufReader::new(inp);
        let mut line = String::new();
        loop {
            line.clear();
            reader.read_line(&mut line).wrap_err("reading debug command line")?;
            let cmd = serde_json::from_str(&line).wrap_err("parsing debug command JSON")?;
            log::info!("read command: {:?}", cmd);
            self.sender.send(cmd)?;
        }
    }
}
