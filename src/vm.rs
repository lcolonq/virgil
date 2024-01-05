use std::collections::HashMap;

pub enum Instruction {
    // Data
    Lit8(u8),
    Lit16(u16),
    Lit32(u32),
    Lit64(u64),
    LocalAddr,
    GlobalAddr,
    ReadAddr,
    Read8,
    Read16,
    Read32,
    Read64,
    Write,
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Trunc8,
    Trunc16,
    Trunc32,
    // Stack manipulation
    Dup,
    Swap,
    Drop,
    // Control flow
    Here,
    Jump,
    JumpIf,
    // Subroutines
    Call,
    Return,
    // Miscellaneous
    Dump,
}

#[derive(Debug, Clone)]
pub enum IntegerSize {
    Bits8,
    Bits16,
    Bits32,
    Bits64,
}

impl IntegerSize {
    pub fn new(bits: u64) -> Self {
        match bits {
            8 => Self::Bits8,
            16 => Self::Bits16,
            32 => Self::Bits32,
            64 => Self::Bits64,
            _ => panic!("invalid integer size: {}", bits),
        }
    }
    pub fn bits(&self) -> u64 {
        match self {
            Self::Bits8 => 8,
            Self::Bits16 => 16,
            Self::Bits32 => 32,
            Self::Bits64 => 64,
        }
    }
    pub fn max(x: &Self, y: &Self) -> Self {
        Self::new(x.bits().max(y.bits()))
    }
    pub fn truncate(&self, x: u64) -> Value {
        match self {
            Self::Bits8 => Value::U8((x & 0xff) as u8),
            Self::Bits16 => Value::U16((x & 0xffff) as u16),
            Self::Bits32 => Value::U32((x & 0xffffffff) as u32),
            Self::Bits64 => Value::U64(x),
        }
    }
}

#[derive(Debug, Clone)]
pub enum MemValue {
    LocalOffset(u64),
    GlobalOffset(u64),
    PC(u64),
    U8(u8),
}

#[derive(Debug, Clone)]
pub enum Value {
    LocalOffset(u64),
    GlobalOffset(u64),
    PC(u64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
}

impl Value {
    pub fn to_memvalues(&self) -> Vec<MemValue> {
        match self {
            Value::GlobalOffset(x) => vec![MemValue::GlobalOffset(*x)],
            Value::LocalOffset(x) => vec![MemValue::LocalOffset(*x)],
            Value::PC(x) => vec![MemValue::PC(*x)],
            Value::U8(x) => vec![MemValue::U8(*x)],
            Value::U16(x) => vec![
                MemValue::U8(((x >> 8) & 0xff) as u8),
                MemValue::U8((x & 0xff) as u8)
            ],
            Value::U32(x) => vec![
                MemValue::U8(((x >> 24) & 0xff) as u8),
                MemValue::U8(((x >> 16) & 0xff) as u8),
                MemValue::U8(((x >> 8) & 0xff) as u8),
                MemValue::U8((x & 0xff) as u8)
            ],
            Value::U64(x) => vec![
                MemValue::U8(((x >> 56) & 0xff) as u8),
                MemValue::U8(((x >> 48) & 0xff) as u8),
                MemValue::U8(((x >> 40) & 0xff) as u8),
                MemValue::U8(((x >> 32) & 0xff) as u8),
                MemValue::U8(((x >> 24) & 0xff) as u8),
                MemValue::U8(((x >> 16) & 0xff) as u8),
                MemValue::U8(((x >> 8) & 0xff) as u8),
                MemValue::U8((x & 0xff) as u8)
            ],
        }
    }
    pub fn to_integer_size(&self) -> IntegerSize {
        match self {
            Value::U8(_) => IntegerSize::Bits8,
            Value::U16(_) => IntegerSize::Bits16,
            Value::U32(_) => IntegerSize::Bits32,
            Value::U64(_) => IntegerSize::Bits64,
            _ => panic!("attempt to get size of address value"),
        }
    }
    pub fn to_offset(&self) -> u64 {
        match self {
            Value::U8(x) => *x as u64,
            Value::U16(x) => *x as u64,
            Value::U32(x) => *x as u64,
            Value::U64(x) => *x as u64,
            _ => panic!("attempt to convert invalid value to offset"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Memory {
    pub contents: HashMap<u64, MemValue>
}

impl Memory {
    fn new() -> Self {
        Self {
            contents: HashMap::new(),
        }
    }
}

pub struct Frame {
    pub locals: Memory,
    pub return_pc: u64,
}

impl Frame {
    pub fn new(return_pc: u64) -> Self {
        Self {
            locals: Memory::new(),
            return_pc,
        }
    }
}

pub struct State {
    pub stack: Vec<Value>,
    pub globals: Memory,
    pub control: Vec<Frame>,
}

impl State {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            globals: Memory::new(),
            control: vec![Frame::new(0x1337)],
        }
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().expect("stack underflow")
    }

    fn push(&mut self, v: Value) {
        self.stack.push(v);
    }

    fn frame(&self) -> &Frame {
        self.control.get(0).expect("control stack underflow")
    }

    fn frame_mut(&mut self) -> &mut Frame {
        self.control.get_mut(0).expect("control stack underflow")
    }

    fn addr_to_memoff<'a>(&'a self, v: Value) -> (&'a Memory, u64) {
        match v {
            Value::GlobalOffset(o) => (&self.globals, o),
            Value::LocalOffset(o) => (&self.frame().locals, o),
            _ => panic!("value is not address: {:?}", v),
        }
    }

    fn addr_to_memoff_mut<'a>(&'a mut self, v: Value) -> (&'a mut Memory, u64) {
        match v {
            Value::GlobalOffset(o) => (&mut self.globals, o),
            Value::LocalOffset(o) => (&mut self.frame_mut().locals, o),
            _ => panic!("value is not address: {:?}", v),
        }
    }

    fn write(&mut self, v: Value, addr: Value) {
        let (mem, o) = self.addr_to_memoff_mut(addr);
        let mvs = v.to_memvalues();
        for (i, mv) in mvs.iter().enumerate() {
            mem.contents.insert(o + (i as u64), mv.clone());
        }
    }

    fn read_byte(mem: &Memory, off: u64) -> u8 {
        let v = mem.contents.get(&off).expect(&format!("failed to read unintialized memory: {:?}", off));
        match v {
            MemValue::U8(x) => *x,
            _ => panic!("tried to read address as 8 bits: {:?}", v),
        }
    }

    fn read_addr(&self, v: Value) -> Value {
        let (mem, o) = self.addr_to_memoff(v);
        let v = mem.contents.get(&o).expect(&format!("failed to read unintialized memory: {:?}", o));
        match v {
            MemValue::LocalOffset(x) => Value::LocalOffset(*x),
            MemValue::GlobalOffset(x) => Value::GlobalOffset(*x),
            MemValue::PC(x) => Value::PC(*x),
            _ => panic!("tried to read data as address: {:?}", v),
        }
    }

    fn read8(&self, v: Value) -> Value {
        let (mem, o) = self.addr_to_memoff(v);
        Value::U8(Self::read_byte(mem, o))
    }

    fn read16(&self, v: Value) -> Value {
        let (mem, o) = self.addr_to_memoff(v);
        Value::U16(
            (Self::read_byte(mem, o) as u16) << 8
                | (Self::read_byte(mem, o + 1) as u16)
        )
    }

    fn read32(&self, v: Value) -> Value {
        let (mem, o) = self.addr_to_memoff(v);
        Value::U32(
            (Self::read_byte(mem, o) as u32) << 24
                | (Self::read_byte(mem, o + 1) as u32) << 16
                | (Self::read_byte(mem, o + 2) as u32) << 8
                | (Self::read_byte(mem, o + 3) as u32)
        )
    }

    fn read64(&self, v: Value) -> Value {
        let (mem, o) = self.addr_to_memoff(v);
        Value::U64(
            (Self::read_byte(mem, o) as u64) << 56
                | (Self::read_byte(mem, o + 1) as u64) << 48
                | (Self::read_byte(mem, o + 2) as u64) << 40
                | (Self::read_byte(mem, o + 3) as u64) << 32
                | (Self::read_byte(mem, o + 4) as u64) << 24
                | (Self::read_byte(mem, o + 5) as u64) << 16
                | (Self::read_byte(mem, o + 6) as u64) << 8
                | (Self::read_byte(mem, o + 7) as u64)
        )
    }

    fn trunc8(&self, v: Value) -> Value {
        match v {
            Value::U8(x) => Value::U8(x as u8),
            Value::U16(x) => Value::U8(x as u8),
            Value::U32(x) => Value::U8(x as u8),
            Value::U64(x) => Value::U8(x as u8),
            _ => panic!("attempted to truncate address: {:?}", v),
        }
    }

    fn trunc16(&self, v: Value) -> Value {
        match v {
            Value::U8(x) => Value::U16(x as u16),
            Value::U16(x) => Value::U16(x as u16),
            Value::U32(x) => Value::U16(x as u16),
            Value::U64(x) => Value::U16(x as u16),
            _ => panic!("attempted to truncate address: {:?}", v),
        }
    }

    fn trunc32(&self, v: Value) -> Value {
        match v {
            Value::U8(x) => Value::U32(x as u32),
            Value::U16(x) => Value::U32(x as u32),
            Value::U32(x) => Value::U32(x as u32),
            Value::U64(x) => Value::U32(x as u32),
            _ => panic!("attempted to truncate address: {:?}", v),
        }
    }

    pub fn run_instruction(&mut self, ins: &Instruction, pc: u64) -> u64 {
        match ins {
            Instruction::Lit8(v) => {
                self.push(Value::U8(*v));
                pc + 1
            },
            Instruction::Lit16(v) => {
                self.push(Value::U16(*v));
                pc + 1
            },
            Instruction::Lit32(v) => {
                self.push(Value::U32(*v));
                pc + 1
            },
            Instruction::Lit64(v) => {
                self.push(Value::U64(*v));
                pc + 1
            },
            Instruction::LocalAddr => {
                self.push(Value::LocalOffset(0));
                pc + 1
            },
            Instruction::GlobalAddr => {
                self.push(Value::GlobalOffset(0));
                pc + 1
            },
            Instruction::ReadAddr => {
                let addr = self.pop();
                self.push(self.read_addr(addr));
                pc + 1
            },
            Instruction::Read8 => {
                let addr = self.pop();
                self.push(self.read8(addr));
                pc + 1
            },
            Instruction::Read16 => {
                let addr = self.pop();
                self.push(self.read16(addr));
                pc + 1
            },
            Instruction::Read32 => {
                let addr = self.pop();
                self.push(self.read32(addr));
                pc + 1
            },
            Instruction::Read64 => {
                let addr = self.pop();
                self.push(self.read64(addr));
                pc + 1
            },
            Instruction::Write => {
                let v = self.pop();
                let addr = self.pop();
                self.write(v, addr);
                pc + 1
            },
            Instruction::Add => {
                let x = self.pop();
                let y = self.pop();
                let v = match (y, x) {
                    (Value::GlobalOffset(b), off) => Value::GlobalOffset(b + off.to_offset()),
                    (Value::LocalOffset(b), off) => Value::LocalOffset(b + off.to_offset()),
                    (Value::PC(b), off) => Value::PC(b + off.to_offset()),
                    (u, v) => {
                        let size = IntegerSize::max(&u.to_integer_size(), &v.to_integer_size());
                        size.truncate(u.to_offset() + v.to_offset())
                    }
                };
                self.push(v);
                pc + 1
            },
            Instruction::Sub => {
                let x = self.pop();
                let y = self.pop();
                let v = match (y, x) {
                    (Value::GlobalOffset(b), off) => Value::GlobalOffset(b - off.to_offset()),
                    (Value::LocalOffset(b), off) => Value::LocalOffset(b - off.to_offset()),
                    (Value::PC(b), off) => Value::PC(b - off.to_offset()),
                    (u, v) => {
                        let size = IntegerSize::max(&u.to_integer_size(), &v.to_integer_size());
                        size.truncate(u.to_offset() - v.to_offset())
                    }
                };
                self.push(v);
                pc + 1
            },
            Instruction::Mul => {
                let x = self.pop();
                let y = self.pop();
                let v = match (y, x) {
                    (Value::GlobalOffset(b), off) => Value::GlobalOffset(b * off.to_offset()),
                    (Value::LocalOffset(b), off) => Value::LocalOffset(b * off.to_offset()),
                    (Value::PC(b), off) => Value::PC(b * off.to_offset()),
                    (u, v) => {
                        let size = IntegerSize::max(&u.to_integer_size(), &v.to_integer_size());
                        size.truncate(u.to_offset() * v.to_offset())
                    }
                };
                self.push(v);
                pc + 1
            },
            Instruction::Div => {
                let x = self.pop();
                let y = self.pop();
                let v = match (y, x) {
                    (Value::GlobalOffset(b), off) => Value::GlobalOffset(b / off.to_offset()),
                    (Value::LocalOffset(b), off) => Value::LocalOffset(b / off.to_offset()),
                    (Value::PC(b), off) => Value::PC(b * off.to_offset()),
                    (u, v) => {
                        let size = IntegerSize::max(&u.to_integer_size(), &v.to_integer_size());
                        size.truncate(u.to_offset() / v.to_offset())
                    }
                };
                self.push(v);
                pc + 1
            },
            Instruction::Mod => {
                let x = self.pop();
                let y = self.pop();
                let v = match (y, x) {
                    (Value::GlobalOffset(b), off) => Value::GlobalOffset(b % off.to_offset()),
                    (Value::LocalOffset(b), off) => Value::LocalOffset(b % off.to_offset()),
                    (Value::PC(b), off) => Value::PC(b % off.to_offset()),
                    (u, v) => {
                        let size = IntegerSize::max(&u.to_integer_size(), &v.to_integer_size());
                        size.truncate(u.to_offset() % v.to_offset())
                    }
                };
                self.push(v);
                pc + 1
            },
            Instruction::Trunc8 => {
                let x = self.pop();
                self.push(self.trunc8(x));
                pc + 1
            },
            Instruction::Trunc16 => {
                let x = self.pop();
                self.push(self.trunc16(x));
                pc + 1
            },
            Instruction::Trunc32 => {
                let x = self.pop();
                self.push(self.trunc32(x));
                pc + 1
            },
            Instruction::Dup => {
                let x = self.pop();
                self.push(x.clone());
                self.push(x);
                pc + 1
            },
            Instruction::Swap => {
                let x = self.pop();
                let y = self.pop();
                self.push(x);
                self.push(y);
                pc + 1
            },
            Instruction::Drop => {
                let _ = self.pop();
                pc + 1
            },
            Instruction::Here => {
                self.push(Value::PC(pc));
                pc + 1
            },
            Instruction::Jump => {
                let t = self.pop();
                if let Value::PC(x) = t {
                    x
                } else {
                    panic!("attempted to jump to non-address value: {:?}", t);
                }
            },
            Instruction::JumpIf => {
                let c = self.pop();
                let mpc = self.pop();
                if c.to_offset() != 0 {
                    if let Value::PC(x) = mpc {
                        x
                    } else {
                        panic!("attempted to jump to non-address value: {:?}", mpc);
                    }
                } else {
                    pc + 1
                }
            },
            Instruction::Call => {
                let t = self.pop();
                if let Value::PC(x) = t {
                    self.control.push(Frame::new(pc + 1));
                    x
                } else {
                    panic!("attempted to call non-address value: {:?}", t);
                }
            },
            Instruction::Return => {
                if let Some(f) = self.control.pop() {
                    f.return_pc
                } else {
                    panic!("control stack underflow");
                }
            },
            Instruction::Dump => {
                let x = self.pop();
                log::info!("DUMP: {:?}", x);
                pc + 1
            },
        }
    }
}

pub struct Program {
    pub pc: u64,
    pub instructions: Vec<Instruction>,
}

impl Program {
    pub fn new(instructions: Vec<Instruction>) -> Self {
        Self {
            pc: 0,
            instructions,
        }
    }
    pub fn reset(&mut self) {
        self.pc = 0;
    }
    pub fn step(&mut self, vm: &mut State) -> bool {
        if let Some(ins) = self.instructions.get(self.pc as usize) {
            self.pc = vm.run_instruction(ins, self.pc);
            true
        } else { false }
    }
    pub fn run(&mut self, vm: &mut State) {
        while self.step(vm) {}
    }
}
