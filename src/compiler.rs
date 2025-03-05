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

    pub fn sizeof(&self, _vm: &State) -> u64 {
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
            // _ => panic!("unsupported type in sizeof"),
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

pub struct Breakable {
    pub breaks: Vec<u64>, // vector of locations of all break NOPs that must be replaced with the end-of-loop address literal instruction
}

pub struct Instructions {
    pub emit_init: bool,
    pub instructions: Vec<vm::Instruction>,
    pub instructions_init: Vec<vm::Instruction>,
}

impl Instructions {
    fn tructions(&mut self) -> &mut Vec<vm::Instruction> {
        if self.emit_init {
            &mut self.instructions_init
        } else {
            &mut self.instructions
        }
    }
}

pub struct State {
    pub functions: HashMap<String, u64>,
    pub globals: Scope,
    pub ins: Instructions,
    pub block_scopes: Vec<Scope>,
    pub breakables: Vec<Breakable>,
    pub typedefs: HashMap<String, Type>,
}

fn declarator_identifier(d: &ast::Declarator) -> String {
    if let ast::DeclaratorKind::Identifier(i) = &d.kind.node {
        i.node.name.clone()
    } else {
        panic!("failed to extract name of definition")
    }
}

fn initdeclarator_expression(d: &ast::InitDeclarator) -> Option<ast::Expression> {
    let i = d.initializer.as_ref()?;
    match &i.node {
        ast::Initializer::Expression(e) => Some(e.node.clone()),
        _ => None,
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
        ast::BinaryOperator::Index => true,
        _ => false,
    }
}

impl State {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            ins: Instructions {
                emit_init: false,
                instructions: Vec::new(),
                instructions_init: Vec::new(),
            },
            globals: Scope { offset: 0, entries: HashMap::new() },
            block_scopes: Vec::new(),
            breakables: Vec::new(),
            typedefs: HashMap::new(),
        }
    }

    pub fn finalize(&self) -> (u64, Vec<vm::Instruction>) {
        let main = *self.functions.get("main").expect("no main function");
        let entry = self.ins.instructions.len();
        let mut ins = self.ins.instructions.clone();
        ins.append(&mut self.ins.instructions_init.clone());
        ins.push(vm::Instruction::Program);
        ins.push(vm::Instruction::Lit64(main));
        ins.push(vm::Instruction::Add);
        ins.push(vm::Instruction::Call);
        (entry as _, ins)
    }

    pub fn load(&mut self, path: &str) {
        let config = lang_c::driver::Config::default();
        self.compile_translation_unit(lang_c::driver::parse(&config, path).expect("failed to parse input").unit);
    }

    fn pc(&mut self) -> u64 {
        self.ins.tructions().len() as u64
    }

    fn sizeof(&self, t: &Type) -> u64 {
        t.sizeof(self)
    }

    fn literal(&self, x: u64) -> vm::Instruction {
        if x <= 0xff {
            vm::Instruction::Lit8(x as _)
        } else if x <= 0xffff {
            vm::Instruction::Lit16(x as _)
        } else if x <= 0xffffffff {
            vm::Instruction::Lit32(x as _)
        } else {
            vm::Instruction::Lit64(x)
        }
    }

    fn start_breakable(&mut self) {
        self.breakables.push(Breakable {
            breaks: Vec::new(),
        });
    }

    fn gen_break(&mut self) {
        let Some(br) = self.breakables.last_mut() else {
            panic!("attempted to break outside of loop/switch");
        };
        self.ins.tructions().push(vm::Instruction::Program);
        let nop = self.ins.tructions().len();
        self.ins.tructions().push(vm::Instruction::Nop);
        self.ins.tructions().push(vm::Instruction::Add);
        self.ins.tructions().push(vm::Instruction::Jump);
        br.breaks.push(nop as _);
    }

    fn end_breakable(&mut self, end: u64) {
        let Some(br) = self.breakables.pop() else {
            panic!("breakable stack underflow");
        };
        for i in br.breaks {
            self.ins.tructions()[i as usize] = self.literal(end);
        }
    }

    fn gen_push_var_addr(&mut self, nm: &str) -> Type {
        for sc in &self.block_scopes {
            if let Some(e) = sc.entries.get(nm) {
                self.ins.tructions().push(vm::Instruction::LocalAddr);
                self.ins.tructions().push(vm::Instruction::Lit64(e.offset));
                self.ins.tructions().push(vm::Instruction::Add);
                return e.ty.clone();
            }
        }
        if let Some(e) = self.globals.entries.get(nm) {
            self.ins.tructions().push(vm::Instruction::GlobalAddr);
            self.ins.tructions().push(vm::Instruction::Lit64(e.offset));
            self.ins.tructions().push(vm::Instruction::Add);
            return e.ty.clone();
        }
        if let Some(f) = self.functions.get(nm) {
            self.ins.tructions().push(vm::Instruction::Program);
            self.ins.tructions().push(vm::Instruction::Lit64(*f));
            self.ins.tructions().push(vm::Instruction::Add);
            return Type::Char; // TODO
        }
        panic!("failed to find variable: {:?}", nm)
    }

    fn gen_read_type(&mut self, ty: &Type) {
        match self.sizeof(ty) {
            1 => self.ins.tructions().push(vm::Instruction::Read8),
            2 => self.ins.tructions().push(vm::Instruction::Read16),
            4 => self.ins.tructions().push(vm::Instruction::Read32),
            8 => self.ins.tructions().push(vm::Instruction::Read64),
            sz => panic!("cannot read variable with size: {:?}", sz),
        }
    }

    fn gen_trunc_type(&mut self, ty: &Type) {
        match self.sizeof(ty) {
            1 => self.ins.tructions().push(vm::Instruction::Trunc8),
            2 => self.ins.tructions().push(vm::Instruction::Trunc16),
            4 => self.ins.tructions().push(vm::Instruction::Trunc32),
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
        let mut mtys = None;
        for s in d.specifiers.iter() {
            if let ast::DeclarationSpecifier::TypeSpecifier(t) = &s.node {
                mtys = Some(&t.node);
                break;
            }
        }
        let tys = mtys.expect("failed to find type in declaration");
        let ty = Type::from_specifier(tys);
        let sz = self.sizeof(&ty);
        let (scope, base, init) = if let Some(l) = self.block_scopes.last_mut() {
            (l, vm::Instruction::LocalAddr, false)
        } else {
            (&mut self.globals, vm::Instruction::GlobalAddr, true)
        };
        let mut offset = scope.offset;
        scope.offset = offset;
        let entries: Vec<(String, u64, Option<ast::Expression>)> = d.declarators.iter().map(|n| {
            let nm = declarator_identifier(&n.node.declarator.node);
            let oexp = initdeclarator_expression(&n.node);
            let ret = (nm, offset, oexp);
            offset += sz;
            ret
        }).collect();
        if let ast::DeclarationSpecifier::StorageClass(s) = &d.specifiers[0].node {
            match s.node {
                ast::StorageClassSpecifier::Typedef => {
                    for (nm, _, _) in entries {
                        self.typedefs.insert(nm.clone(), ty.clone());
                    }
                    return;
                },
                _ => {}
            }
        }
        for (nm, off, _oexp) in &entries {
            scope.entries.insert(nm.clone(), Entry { offset: *off, ty: ty.clone() });
        }
        for (_nm, off, oexp) in &entries {
            if let Some(exp) = oexp {
                self.ins.emit_init = init;
                self.ins.tructions().push(base.clone());
                self.ins.tructions().push(vm::Instruction::Lit64(*off));
                self.ins.tructions().push(vm::Instruction::Add);
                self.compile_expression(exp.clone());
                self.gen_trunc_type(&ty);
                self.ins.tructions().push(vm::Instruction::Write);
                self.ins.emit_init = false;
            }
        }
    }

    fn compile_definition(&mut self, d: ast::FunctionDefinition) {
        let name = declarator_identifier(&d.declarator.node);
        let pc = self.pc();
        self.functions.insert(name.clone(), pc);
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
            self.ins.tructions().push(vm::Instruction::LocalAddr);
            self.ins.tructions().push(vm::Instruction::Lit64(p.offset));
            self.ins.tructions().push(vm::Instruction::Add);
            self.ins.tructions().push(vm::Instruction::Swap);
            self.ins.tructions().push(vm::Instruction::Write);
        }
        self.compile_statement(d.statement.node);
        self.block_scopes.pop();
        self.ins.tructions().push(vm::Instruction::Return);
    }

    // neither produces or consumes stack
    fn compile_statement(&mut self, d: ast::Statement) {
        match d {
            ast::Statement::Expression(mn) => {
                if let Some(n) = mn {
                    self.compile_expression(n.node);
                    self.ins.tructions().push(vm::Instruction::Dump);
                }
            },
            ast::Statement::Return(me) => {
                if let Some(e) = me {
                    self.compile_expression(e.node)
                }
                self.ins.tructions().push(vm::Instruction::Return);
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
            ast::Statement::If(i) => {
                self.compile_expression(i.node.condition.node);
                self.ins.tructions().push(vm::Instruction::Not);
                self.ins.tructions().push(vm::Instruction::Program);
                let jmp = self.ins.tructions().len();
                self.ins.tructions().push(vm::Instruction::Nop);
                self.ins.tructions().push(vm::Instruction::Add);
                self.ins.tructions().push(vm::Instruction::Swap);
                self.ins.tructions().push(vm::Instruction::JumpIf);
                self.compile_statement(i.node.then_statement.node);
                self.ins.tructions().push(vm::Instruction::Program);
                let endjmp = self.ins.tructions().len();
                self.ins.tructions().push(vm::Instruction::Nop);
                self.ins.tructions().push(vm::Instruction::Add);
                self.ins.tructions().push(vm::Instruction::Jump);
                let here = self.ins.tructions().len();
                self.ins.tructions()[jmp] = self.literal(here as _);
                if let Some(els) = i.node.else_statement {
                    self.compile_statement(els.node);
                }
                let here = self.ins.tructions().len();
                self.ins.tructions()[endjmp] = self.literal(here as _);
            },
            ast::Statement::While(w) => {
                let start = self.ins.tructions().len() as u64;
                self.compile_expression(w.node.expression.node);
                self.ins.tructions().push(vm::Instruction::Not);
                self.ins.tructions().push(vm::Instruction::Program);
                let jmp = self.ins.tructions().len();
                self.ins.tructions().push(vm::Instruction::Nop);
                self.ins.tructions().push(vm::Instruction::Add);
                self.ins.tructions().push(vm::Instruction::Swap);
                self.ins.tructions().push(vm::Instruction::JumpIf);
                self.start_breakable();
                self.compile_statement(w.node.statement.node);
                self.ins.tructions().push(vm::Instruction::Program);
                let lit = self.literal(start);
                self.ins.tructions().push(lit);
                self.ins.tructions().push(vm::Instruction::Add);
                self.ins.tructions().push(vm::Instruction::Jump);
                let end = self.ins.tructions().len() as u64;
                self.ins.tructions()[jmp] = self.literal(end);
                self.end_breakable(end);
            }
            _ => panic!("unsupported statement: {:?}", d),
        }
    }

    // like compile_expression, but pushes an address to the stack rather than a value
    fn compile_expression_lvalue(&mut self, e: ast::Expression) -> Type {
        match e {
            ast::Expression::Identifier(i) => self.gen_push_var_addr(&i.node.name),
            ast::Expression::BinaryOperator(boe) => {
                match boe.node.operator.node {
                    ast::BinaryOperator::Index => {
                        let ty = self.compile_expression_lvalue(boe.node.lhs.node);
                        let sz = ty.sizeof(self);
                        self.compile_expression(boe.node.rhs.node);
                        self.ins.tructions().push(vm::Instruction::Lit64(sz));
                        self.ins.tructions().push(vm::Instruction::Mul);
                        self.ins.tructions().push(vm::Instruction::Add);
                        ty // todo maybe fucked
                    },
                    bop => panic!("unsupported binary operator in lvalue context: {:?}", bop),
                }
            },
            _ => {
                self.compile_expression(e);
                Type::Int
            },
        }
    }

    // pushes a single result value to the stack
    fn compile_expression(&mut self, e: ast::Expression) {
        match e {
            ast::Expression::Constant(c) => match c.node {
                ast::Constant::Integer(i) => {
                    let val = i.number.parse().expect("failed to parse literal");
                    self.ins.tructions().push(vm::Instruction::Lit64(val));
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
                match &ce.node.callee.node {
                    ast::Expression::Identifier(i) if i.node.name == "syscall" => {
                        self.ins.tructions().push(vm::Instruction::Syscall);
                    },
                    _ => {
                        self.compile_expression_lvalue(ce.node.callee.node);
                        self.ins.tructions().push(vm::Instruction::Call);
                    }
                }
            },
            ast::Expression::UnaryOperator(uoe) => {
                match uoe.node.operator.node {
                    ast::UnaryOperator::Address => {
                        let _ = self.compile_expression_lvalue(uoe.node.operand.node);
                    },
                    uop => panic!("unsupported binary operator (with lvalue): {:?}", uop),
                }
            },
            ast::Expression::BinaryOperator(boe) => {
                if binop_has_lvalue(&boe.node.operator.node) {
                    let ty = self.compile_expression_lvalue(boe.node.lhs.node);
                    self.compile_expression(boe.node.rhs.node);
                    match boe.node.operator.node {
                        ast::BinaryOperator::Assign => {
                            self.gen_trunc_type(&ty);
                            self.ins.tructions().push(vm::Instruction::Dup);
                            self.ins.tructions().push(vm::Instruction::Rot);
                            self.ins.tructions().push(vm::Instruction::Write)
                        },
                        ast::BinaryOperator::Index => {
                            let sz = ty.sizeof(self);
                            self.ins.tructions().push(vm::Instruction::Lit64(sz));
                            self.ins.tructions().push(vm::Instruction::Mul);
                            self.ins.tructions().push(vm::Instruction::Add);
                            self.gen_read_type(&ty);
                        },
                        bop => panic!("unsupported binary operator (with lvalue): {:?}", bop),
                    }
                } else {
                    self.compile_expression(boe.node.lhs.node);
                    self.compile_expression(boe.node.rhs.node);
                    match boe.node.operator.node {
                        ast::BinaryOperator::Plus => self.ins.tructions().push(vm::Instruction::Add),
                        ast::BinaryOperator::Minus => self.ins.tructions().push(vm::Instruction::Sub),
                        ast::BinaryOperator::Multiply => self.ins.tructions().push(vm::Instruction::Mul),
                        ast::BinaryOperator::Less => self.ins.tructions().push(vm::Instruction::Less),
                        bop => panic!("unsupported binary operator (no lvalue): {:?}", bop),
                    }
                }
            },
            _ => panic!("unsupported expression: {:?}", e),
        }
    }
}
