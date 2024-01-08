use crate::vm;

use std::collections::HashMap;
use lang_c::ast as ast;

#[derive(Debug, Clone)]
pub enum Type {
    Void,
    Char,
    Short,
    Int,
    Long,
    Float,
    Double,
    Signed,
    Unsigned,
    Bool,
}

impl Type {
    pub fn from_specifier(spec: &lang_c::ast::TypeSpecifier) -> Self {
        match spec {
            ast::TypeSpecifier::Void => Self::Void,
            ast::TypeSpecifier::Char => Self::Char,
            ast::TypeSpecifier::Short => Self::Short,
            ast::TypeSpecifier::Int => Self::Int,
            ast::TypeSpecifier::Long => Self::Long,
            ast::TypeSpecifier::Float => Self::Float,
            ast::TypeSpecifier::Double => Self::Double,
            ast::TypeSpecifier::Signed => Self::Signed,
            ast::TypeSpecifier::Unsigned => Self::Unsigned,
            ast::TypeSpecifier::Bool => Self::Bool,
            _ => panic!("unsupported type"),
        }
    }

    pub fn sizeof(&self, vm: &State) -> u64 {
        match self {
            Self::Void => 0,
            Self::Char => 1,
            Self::Short => 2,
            Self::Int => 4,
            Self::Long => 8,
            Self::Float => 4,
            Self::Double => 8,
            Self::Signed => 4,
            Self::Unsigned => 4,
            Self::Bool => 1,
            _ => panic!("unsupported type in sizeof"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Entry {
    pub offset: u64,
    pub ty: Type,
}

pub struct Scope {
    pub offset: u64,
    pub entries: HashMap<String, Entry>,
}

pub struct State {
    pub functions: HashMap<String, u64>,
    pub instructions: Vec<vm::Instruction>,
    pub globals: Scope,
    pub block_scopes: Vec<Scope>,
}

fn declarator_identifier(d: &ast::Declarator) -> String {
    if let ast::DeclaratorKind::Identifier(i) = &d.kind.node {
        i.node.name.clone()
    } else {
        panic!("failed to extract name of definition")
    }
}

fn binop_has_lvalue(b: &ast::BinaryOperator) -> bool {
    match b {
        ast::BinaryOperator::Assign => true,
        ast::BinaryOperator::AssignBitwiseAnd => true,
        ast::BinaryOperator::AssignBitwiseOr => true,
        ast::BinaryOperator::AssignBitwiseXor => true,
        ast::BinaryOperator::AssignDivide => true,
        ast::BinaryOperator::AssignMinus => true,
        ast::BinaryOperator::AssignModulo => true,
        ast::BinaryOperator::AssignMultiply => true,
        ast::BinaryOperator::AssignPlus => true,
        ast::BinaryOperator::AssignShiftLeft => true,
        ast::BinaryOperator::AssignShiftRight => true,
        _ => false,
    }
}

impl State {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            instructions: Vec::new(),
            globals: Scope { offset: 0, entries: HashMap::new() },
            block_scopes: Vec::new(),
        }
    }

    pub fn load(&mut self, path: &str) {
        let config = lang_c::driver::Config::default();
        self.compile_translation_unit(lang_c::driver::parse(&config, path).expect("failed to parse input").unit);
    }

    fn pc(&self) -> u64 {
        self.instructions.len() as u64
    }

    fn sizeof(&self, t: &Type) -> u64 {
        t.sizeof(self)
    }

    fn gen_push_var_addr(&mut self, nm: &str) -> Type {
        for sc in &self.block_scopes {
            if let Some(e) = sc.entries.get(nm) {
                self.instructions.push(vm::Instruction::LocalAddr);
                self.instructions.push(vm::Instruction::Lit64(e.offset));
                self.instructions.push(vm::Instruction::Add);
                return e.ty.clone();
            }
        }
        if let Some(e) = self.globals.entries.get(nm) {
            self.instructions.push(vm::Instruction::GlobalAddr);
            self.instructions.push(vm::Instruction::Lit64(e.offset));
            self.instructions.push(vm::Instruction::Add);
            return e.ty.clone();
        }
        if let Some(f) = self.functions.get(nm) {
            self.instructions.push(vm::Instruction::Program);
            self.instructions.push(vm::Instruction::Lit64(*f));
            self.instructions.push(vm::Instruction::Add);
            return Type::Char; // TODO
        }
        panic!("failed to find variable: {:?}", nm)
    }

    fn gen_read_type(&mut self, ty: &Type) {
        match self.sizeof(ty) {
            1 => self.instructions.push(vm::Instruction::Read8),
            2 => self.instructions.push(vm::Instruction::Read16),
            4 => self.instructions.push(vm::Instruction::Read32),
            8 => self.instructions.push(vm::Instruction::Read64),
            sz => panic!("cannot read variable with size: {:?}", sz),
        }
    }

    fn gen_trunc_type(&mut self, ty: &Type) {
        match self.sizeof(ty) {
            1 => self.instructions.push(vm::Instruction::Trunc8),
            2 => self.instructions.push(vm::Instruction::Trunc16),
            4 => self.instructions.push(vm::Instruction::Trunc32),
            _ => {},
        }
    }

    fn compile_translation_unit(&mut self, tu: ast::TranslationUnit) {
        for n in tu.0 {
            self.compile_external_declaration(n.node);
        }
    }

    fn compile_external_declaration(&mut self, ed: ast::ExternalDeclaration) {
        match ed {
            ast::ExternalDeclaration::Declaration(n) => self.compile_declaration(n.node),
            ast::ExternalDeclaration::FunctionDefinition(d) => self.compile_definition(d.node),
            _ => panic!("unsupported language feature"),
        }
    }

    fn compile_declaration(&mut self, d: ast::Declaration) {
        let tys = if let ast::DeclarationSpecifier::TypeSpecifier(t) = &d.specifiers[0].node {
            &t.node
        } else {
            panic!("non-type specifier found")
        };
        let ty = Type::from_specifier(tys);
        let sz = self.sizeof(&ty);
        let scope = if let Some(l) = self.block_scopes.last_mut() {
            l
        } else {
            &mut self.globals
        };
        let mut offset = scope.offset;
        let entries: Vec<(String, u64)> = d.declarators.iter().map(|n| {
            let nm = declarator_identifier(&n.node.declarator.node);
            let ret = (nm, offset);
            offset += sz;
            ret
        }).collect();
        scope.offset = offset;
        for (nm, off) in entries {
            scope.entries.insert(nm, Entry {offset: off, ty: ty.clone()});
        }
    }

    fn compile_definition(&mut self, d: ast::FunctionDefinition) {
        let name = declarator_identifier(&d.declarator.node);
        self.functions.insert(name.clone(), self.pc());
        let mut offset = 0;
        let params: Vec<(String, Entry)> = if let ast::DerivedDeclarator::Function(f) = &d.declarator.node.derived[0].node {
            f.node.parameters.iter().map(|n| {
                let nm = declarator_identifier(&n.node.declarator.as_ref().expect("missing parameter name").node);
                let ty = if let ast::DeclarationSpecifier::TypeSpecifier(t) = &n.node.specifiers[0].node {
                    Type::from_specifier(&t.node)
                } else {
                    panic!("non-type specifier found")
                };
                let ret = (nm, Entry { offset, ty: ty.clone() });
                offset += self.sizeof(&ty);
                ret
            }).collect()
        } else {
            Vec::new()
        };
        self.block_scopes.push(Scope { offset, entries: params.clone().into_iter().collect() });
        for (_, p) in params.iter().rev() {
            self.instructions.push(vm::Instruction::LocalAddr);
            self.instructions.push(vm::Instruction::Lit64(p.offset));
            self.instructions.push(vm::Instruction::Add);
            self.instructions.push(vm::Instruction::Swap);
            self.instructions.push(vm::Instruction::Write);
        }
        self.compile_statement(d.statement.node);
        self.block_scopes.pop();
        self.instructions.push(vm::Instruction::Return);
    }

    // neither produces or consumes stack
    fn compile_statement(&mut self, d: ast::Statement) {
        match d {
            ast::Statement::Expression(mn) => {
                if let Some(n) = mn {
                    self.compile_expression(n.node);
                    self.instructions.push(vm::Instruction::Dump);
                }
            },
            ast::Statement::Return(me) => {
                if let Some(e) = me {
                    self.compile_expression(e.node)
                }
                self.instructions.push(vm::Instruction::Return);
            },
            ast::Statement::Compound(nodes) => {
                let offset = if let Some(sc) = self.block_scopes.last() {
                    sc.offset
                } else {
                    0
                };
                self.block_scopes.push(Scope { offset, entries: HashMap::new() });
                for n in nodes {
                    match n.node {
                        ast::BlockItem::Statement(s) => self.compile_statement(s.node),
                        ast::BlockItem::Declaration(d) => self.compile_declaration(d.node),
                        ast::BlockItem::StaticAssert(_) => panic!("unsupported static assert"),
                    }
                }
                self.block_scopes.pop();
            },
            _ => panic!("unsupported statement: {:?}", d),
        }
    }

    // like compile_expression, but pushes an address to the stack rather than a value
    fn compile_expression_lvalue(&mut self, e: ast::Expression) -> Type {
        match e {
            ast::Expression::Identifier(i) => self.gen_push_var_addr(&i.node.name),
            _ => panic!("invalid lvalue: {:?}", e),
        }
    }

    // pushes a single result value to the stack
    fn compile_expression(&mut self, e: ast::Expression) {
        match e {
            ast::Expression::Constant(c) => match c.node {
                ast::Constant::Integer(i) => {
                    let val = i.number.parse().expect("failed to parse literal");
                    self.instructions.push(vm::Instruction::Lit64(val));
                },
                co => panic!("unsupported literal: {:?}", co),
            },
            ast::Expression::Identifier(i) => {
                let ty = self.gen_push_var_addr(&i.node.name);
                self.gen_read_type(&ty);
            },
            ast::Expression::Call(ce) => {
                for e in ce.node.arguments {
                    self.compile_expression(e.node);
                }
                self.compile_expression_lvalue(ce.node.callee.node);
                self.instructions.push(vm::Instruction::Call);
            },
            ast::Expression::BinaryOperator(boe) => {
                if binop_has_lvalue(&boe.node.operator.node) {
                    let ty = self.compile_expression_lvalue(boe.node.lhs.node);
                    self.compile_expression(boe.node.rhs.node);
                    match boe.node.operator.node {
                        ast::BinaryOperator::Assign => {
                            self.gen_trunc_type(&ty);
                            self.instructions.push(vm::Instruction::Dup);
                            self.instructions.push(vm::Instruction::Rot);
                            self.instructions.push(vm::Instruction::Write)
                        },
                        bop => panic!("unsupported binary operator (with lvalue): {:?}", bop),
                    }
                } else {
                    self.compile_expression(boe.node.lhs.node);
                    self.compile_expression(boe.node.rhs.node);
                    match boe.node.operator.node {
                        ast::BinaryOperator::Plus => self.instructions.push(vm::Instruction::Add),
                        bop => panic!("unsupported binary operator (no lvalue): {:?}", bop),
                    }
                }
            },
            _ => panic!("unsupported expression: {:?}", e),
        }
    }
}
