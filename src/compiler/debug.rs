use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Variable {
    pub nm: String,
    pub ty: super::Type,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub src_start: u64,
    pub src_end: u64,
    pub instructions: std::ops::RangeInclusive<u64>, // what instructions were generated for this statement
}

#[derive(Debug, Clone)]
pub struct Function {
    pub nm: String,
    pub instructions: std::ops::RangeInclusive<u64>,
    pub vars: HashMap<u64, Variable>, // offsets to variables
    pub statements: Vec<Statement>, // all statements
}

#[derive(Debug, Clone)]
pub struct Struct {
}

#[derive(Debug, Clone)]
pub struct Info {
    pub functions: Vec<Function>,
}
impl Info {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }
}
