use std::collections::HashMap;

pub struct Variable {
    pub offset: u64,
    pub ty: super::Type,
}

pub struct Statement {
    pub src_start: u64,
    pub src_end: u64,
    pub instructions: std::ops::RangeInclusive<u64>, // what instructions were generated for this statement
}

pub struct Function {
    pub vars: HashMap<String, Variable>,
    pub statements: Vec<Statement>, // all statements
    pub instruction_statements: Vec<Option<u64>>, // for each instruction, which statement does it belong to, if any??
}

pub struct Struct {
}

pub struct DebugInfo {
}
