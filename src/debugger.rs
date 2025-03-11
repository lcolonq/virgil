use std::{io::{BufRead, BufReader, Read}, sync::mpsc::{channel, Receiver, RecvError, Sender, TryRecvError}};
use serde::{Deserialize, Serialize};

use teleia::*;

use crate::vm;

#[derive(Debug, Serialize, Deserialize)]
pub enum Command {
    Step,
    StepStatement,
    Break(u64),
    BreakStatement,
    Stop,
    Continue,
}

pub enum Mode {
    Paused,
    Running,
}

pub struct Debugger {
    mode: Mode,
    vm: vm::State,
    prog: vm::Program,
    breakpoints: Vec<u64>,
}
impl Debugger {
    pub fn new(entry: u64, ins: Vec<vm::Instruction>) -> Self {
        let mut prog = vm::Program::new(ins);
        prog.pc = entry;
        Self {
            mode: Mode::Paused,
            vm: vm::State::new(),
            prog,
            breakpoints: Vec::new(),
        }
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
            Command::BreakStatement => todo!(),
            Command::Stop => { self.mode = Mode::Paused; },
            Command::Continue => { self.mode = Mode::Running; },
        }
        Ok(())
    }
    pub fn run(&mut self, cmds: Receiver<Command>) -> Erm<()> {
        loop {
            match self.mode {
                Mode::Paused => {
                    match cmds.recv() {
                        Ok(cmd) => self.cmd(cmd)?,
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
