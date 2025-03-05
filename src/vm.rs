use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum Instruction {
    // Cheat lololololololol
    Syscall, // pop number and then do something very fancy based on the number hehe
    // Nop
    Nop,
    // Data
    Lit8(u8),
    Lit16(u16),
    Lit32(u32),
    Lit64(u64),
    Program,
    LocalAddr,
    GlobalAddr,
    ReadAddr,
    Read8,
    Read16,
    Read32,
    Read64,
    Write,
    // Boolean
    Not,
    // Comparison
    Equal,
    Less,
    // LessEqual,
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
    Over,
    Swap,
    Drop,
    Rot,
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

impl Instruction {
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
    HeapOffset(u64, u64),
    PC(u64),
    U8(u8),
}

impl MemValue {
    pub fn as_byte(&self) -> Option<u8> {
        match self {
            Self::U8(b) => Some(*b),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Empty,
    LocalOffset(u64),
    GlobalOffset(u64),
    HeapOffset(u64, u64),
    PC(u64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
}

impl Value {
    pub fn to_memvalues(&self) -> Vec<MemValue> {
        match self {
            Value::Empty => vec![],
            Value::GlobalOffset(x) => vec![MemValue::GlobalOffset(*x)],
            Value::LocalOffset(x) => vec![MemValue::LocalOffset(*x)],
            Value::HeapOffset(id, x) => vec![MemValue::HeapOffset(*id, *x)],
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

#[derive(Debug)]
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

pub struct Allocation {
    pub mem: Memory,
}

pub struct State {
    pub stack: Vec<Value>,
    pub heap: Vec<Allocation>,
    pub globals: Memory,
    pub control: Vec<Frame>,
}

impl State {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            heap: Vec::new(),
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

    fn malloc(&mut self, _size: u64) -> Value {
        self.heap.push(Allocation {
            mem: Memory::new(),
        });
        Value::HeapOffset((self.heap.len() - 1) as u64, 0)
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
            Value::HeapOffset(id, o) => if let Some(a) = self.heap.get(id as usize) {
                (&a.mem, o)
            } else {
                panic!("heap address refers to invalid allocation: {:?}", v)
            },
            _ => panic!("value is not address: {:?}", v),
        }
    }

    fn addr_to_memoff_mut<'a>(&'a mut self, v: Value) -> (&'a mut Memory, u64) {
        match v {
            Value::GlobalOffset(o) => (&mut self.globals, o),
            Value::LocalOffset(o) => (&mut self.frame_mut().locals, o),
            Value::HeapOffset(id, o) => if let Some(a) = self.heap.get_mut(id as usize) {
                (&mut a.mem, o)
            } else {
                panic!("heap address refers to invalid allocation: {:?}", v)
            },
            _ => panic!("value is not address: {:?}", v),
        }
    }

    fn write(&mut self, v: Value, addr: Value) {
        log::info!("write {:?} to {:?}", v, addr);
        let (mem, o) = self.addr_to_memoff_mut(addr);
        let mvs = v.to_memvalues();
        for (i, mv) in mvs.iter().enumerate() {
            mem.contents.insert(o + (i as u64), mv.clone());
        }
    }

    fn read_u32_safe(mem: &Memory, off: u64) -> Option<u32> {
        let p =
            (mem.contents.get(&off)?.as_byte()? as u32) << 24
            | (mem.contents.get(&(off + 1))?.as_byte()? as u32) << 16
            | (mem.contents.get(&(off + 2))?.as_byte()? as u32) << 8
            | (mem.contents.get(&(off + 3))?.as_byte()? as u32);
        Some(p)
    }

    fn read_byte(mem: &Memory, off: u64) -> u8 {
        let v = mem.contents.get(&off).expect(&format!("failed to read unintialized memory: {:?}", off));
        match v {
            MemValue::U8(x) => *x,
            _ => panic!("tried to read address as 8 bits: {:?}", v),
        }
    }

    fn read_string(mem: &Memory, off: u64) -> String {
        let mut buf = Vec::new();
        let mut i = off;
        loop {
            let c = Self::read_byte(mem, i);
            if c == 0 { break; }
            buf.push(c);
            i += 1;
        }
        String::from_utf8(buf).expect("invalid utf-8 string")
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
        // log::info!("read32: {:?}", v);
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
            Instruction::Syscall => {
                let call = self.pop().to_offset();
                match call {
                    0 => { // debug
                        let v = self.pop();
                        log::info!("hello computer: {:?}", v);
                    },
                    1 => { // pixel
                        let v = self.pop();
                        let (mem, base) = self.addr_to_memoff_mut(v);
                        let mut pixels = [0; 640 * 400];
                        for i in 0..(640 * 400) {
                            if let Some(p) = State::read_u32_safe(mem, base + i * 4) {
                                log::info!("pixel found at {}", i);
                                pixels[i as usize] = p;
                            }
                        }
                    },
                    2 => { // malloc
                        let sz = self.pop().to_offset();
                        let ret = self.malloc(sz);
                        self.push(ret);
                    },
                    3 => { // puts
                        let msg_addr = self.pop();
                        let (mem, o) = self.addr_to_memoff(msg_addr);
                        let s = Self::read_string(mem, o);
                        log::info!("puts: {}", s);
                    },
                    _ => {
                        panic!("invalid syscall number: {}", call);
                    }
                }
                pc + 1
            },
            Instruction::Nop => { pc + 1 },
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
            Instruction::Program => {
                self.push(Value::PC(0));
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
            Instruction::Not => {
                let v = self.pop();
                match v {
                    Value::U8(x) => self.push(Value::U8((x == 0) as _)),
                    Value::U16(x) => self.push(Value::U16((x == 0) as _)),
                    Value::U32(x) => self.push(Value::U32((x == 0) as _)),
                    Value::U64(x) => self.push(Value::U64((x == 0) as _)),
                    _ => panic!("attempted to negate non-integer: {:?}", v),
                }
                pc + 1
            },
            Instruction::Equal => {
                let x = self.pop();
                let y = self.pop();
                let v = match (x, y) {
                    (a@Value::GlobalOffset(_), b)
                        | (a, b@Value::GlobalOffset(_))
                        | (a@Value::LocalOffset(_), b)
                        | (a, b@Value::LocalOffset(_))
                        | (a@Value::PC(_), b)
                        | (a, b@Value::PC(_))
                        => Value::U8((a == b) as _),
                    (u, v) => {
                        let size = IntegerSize::max(&u.to_integer_size(), &v.to_integer_size());
                        Value::U8((u.to_offset() == v.to_offset()) as _)
                    }
                };
                self.push(v);
                pc + 1
            },
            Instruction::Less => {
                let y = self.pop();
                let x = self.pop();
                let v = match (x, y) {
                    (Value::GlobalOffset(a), Value::GlobalOffset(b)) => Value::U8((a < b) as _),
                    (Value::LocalOffset(a), Value::LocalOffset(b)) => Value::U8((a < b) as _),
                    (Value::PC(a), Value::PC(b)) => Value::U8((a < b) as _),
                    (u, v) => {
                        let size = IntegerSize::max(&u.to_integer_size(), &v.to_integer_size());
                        Value::U8((u.to_offset() < v.to_offset()) as _)
                    }
                };
                self.push(v);
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
            Instruction::Over => {
                let x = self.pop();
                let y = self.pop();
                self.push(y.clone());
                self.push(x);
                self.push(y);
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
            Instruction::Rot => {
                let x = self.pop();
                let y = self.pop();
                let z = self.pop();
                log::info!("rotating! {:?} {:?} {:?}", x, y, z);
                self.push(x);
                self.push(z);
                self.push(y);
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
                // log::info!("jumpif: {:?} {:?}", c, mpc);
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
        while self.step (vm) {};
    }
}
