use crate::vm;

use std::collections::HashMap;
use lang_c::ast as ast;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompoundEntry {
    ty: Type,
    offset: u64,
    bitfield: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Void,
    Function(Box<Type>), // function pointer with return type
    Pointer(Box<Type>),
    Array(u64, Box<Type>), // array with length
    Struct(u64, HashMap<String, CompoundEntry>),
    Union(u64, HashMap<String, CompoundEntry>),
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
    pub fn from_specifier(vm: &mut State, spec: &lang_c::ast::TypeSpecifier) -> Self {
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
            ast::TypeSpecifier::TypedefName(nm) =>
                vm.typedefs.get(&nm.node.name).expect("could not find typedef").clone(),
            ast::TypeSpecifier::Struct(s) => vm.handle_struct_def(&s.node),
            _ => panic!("unsupported type"),
        }
    }

    pub fn sizeof(&self) -> u64 {
        match self {
            Self::Void => 0,
            Self::Function(_) => 1,
            Self::Pointer(_) => 1,
            Self::Array(len, ty) => len * ty.sizeof(),
            Self::Struct(sz, _) => *sz,
            Self::Union(sz, _) => *sz,
            Self::Char => 1,
            Self::Short => 2,
            Self::Int => 4,
            Self::Long => 8,
            Self::Float => 4,
            Self::Double => 8,
            Self::Signed => 4,
            Self::Unsigned => 4,
            Self::Bool => 1,
            _ => panic!("unsupported type in sizeof: {:?}", self),
        }
    }

    pub fn field_offsets(&self, base: u64, offs: &mut Vec<(u64, Type)>) {
        match self {
            Self::Array(len, ty) => {
                let sz = ty.sizeof();
                for i in 0..*len {
                    ty.field_offsets(base + sz * i, offs);
                }
            },
            Self::Struct(_, fields) => {
                for (_, ent) in fields.iter() {
                    ent.ty.field_offsets(base + ent.offset, offs);
                }
            },
            ty => offs.push((base, ty.clone())),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Entry {
    pub offset: u64,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub offset: u64,
    pub ret: Type,
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
    pub functions: HashMap<String, Function>,
    pub globals: Scope,
    pub ins: Instructions,
    pub block_scopes: Vec<Scope>,
    pub breakables: Vec<Breakable>,
    pub typedefs: HashMap<String, Type>,
    pub structs: HashMap<String, Type>,
    pub unions: HashMap<String, Type>,
}

fn extract_declarator(d: &ast::Declarator, base: &Type) -> (String, Type) {
    let nm = if let ast::DeclaratorKind::Identifier(i) = &d.kind.node {
        i.node.name.clone()
    } else {
        panic!("failed to extract name of definition")
    };
    let mut ty = base.clone();
    for x in &d.derived {
        match &x.node {
            ast::DerivedDeclarator::Pointer(_) => {
                ty = Type::Pointer(Box::new(ty));
            },
            ast::DerivedDeclarator::Array(l) => {
                if let ast::ArraySize::VariableExpression(bve) = &l.node.size {
                    if let ast::Expression::Constant(c) = &bve.node {
                        if let ast::Constant::Integer(i) = &c.node {
                            let len = i.number.parse().expect("failed to parse array size constant");
                            ty = Type::Array(len, Box::new(ty));
                        } else {
                            panic!("array size constant is not an integer");
                        }
                    } else {
                            panic!("array size expression is not constant");
                    }
                } else {
                    panic!("array type does not have size");
                }
            },
            _ => {},
        }
    }
    (nm, ty)
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
            structs: HashMap::new(),
            unions: HashMap::new(),
        }
    }

    pub fn finalize(&self) -> (u64, Vec<vm::Instruction>) {
        let main = self.functions.get("main").expect("no main function");
        let entry = self.ins.instructions.len();
        let mut ins = self.ins.instructions.clone();
        ins.append(&mut self.ins.instructions_init.clone());
        ins.push(vm::Instruction::Program);
        ins.push(vm::Instruction::Lit64(main.offset));
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

    fn handle_struct_def(&mut self, st: &ast::StructType) -> Type {
        let names = match st.kind.node {
            ast::StructKind::Struct => &mut self.structs,
            ast::StructKind::Union => &mut self.unions,
        };
        let snm = st.identifier.as_ref().map(|nid| nid.node.name.clone());
        if let Some(nm) = &snm {
            if let Some(t) = names.get(nm) {
                return t.clone();
            }
        }
        if let Some(decls) = &st.declarations {
            let mut fields = HashMap::new();
            let mut offset = 0;
            let mut totalsz = 0;
            for d in decls {
                if let ast::StructDeclaration::Field(df) = &d.node {
                    let mut mtys = None;
                    for s in df.node.specifiers.iter() {
                        if let ast::SpecifierQualifier::TypeSpecifier(t) = &s.node {
                            mtys = Some(&t.node);
                            break;
                        }
                    }
                    let tys = mtys.expect("failed to find type in specifiers");
                    let base = Type::from_specifier(self, tys);
                    for sdecl in df.node.declarators.iter() {
                        if let Some(decl) = &sdecl.node.declarator {
                            let (nm, ty) = extract_declarator(&decl.node, &base);
                            let sz = ty.sizeof();
                            fields.insert(nm, CompoundEntry {
                                ty,
                                offset,
                                bitfield: None,
                            });
                            match st.kind.node {
                                ast::StructKind::Struct => {
                                    offset += sz;
                                    totalsz += sz;
                                },
                                ast::StructKind::Union => {
                                    totalsz = totalsz.max(sz);
                                },
                            }
                        }
                    }
                }
            }
            return match st.kind.node {
                ast::StructKind::Struct => {
                    let ty = Type::Struct(totalsz, fields);
                    if let Some(nm) = snm { self.structs.insert(nm, ty.clone()); }
                    ty
                },
                ast::StructKind::Union => {
                    let ty = Type::Union(totalsz, fields);
                    if let Some(nm) = snm { self.unions.insert(nm, ty.clone()); }
                    ty
                },
            };
        }
        panic!("could not handle struct type: {:?}", st)
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
            self.ins.tructions().push(vm::Instruction::Lit64(f.offset));
            self.ins.tructions().push(vm::Instruction::Add);
            return Type::Function(Box::new(f.ret.clone()));
        }
        panic!("failed to find variable: {:?}", nm)
    }

    fn gen_read_type(&mut self, ty: &Type) {
        if let Type::Pointer(_) = ty {
            self.ins.tructions().push(vm::Instruction::ReadAddr)
        } else if let Type::Array(_, _) = ty {
            // don't need a read - a "raw" array variable is just the address!
            // self.ins.tructions().push(vm::Instruction::ReadAddr)
        } else if let Type::Struct(_, _) = ty {
            // don't need a read - we handle dereferencing struct locations at use sites
        } else {
            match ty.sizeof() {
                1 => self.ins.tructions().push(vm::Instruction::Read8),
                2 => self.ins.tructions().push(vm::Instruction::Read16),
                4 => self.ins.tructions().push(vm::Instruction::Read32),
                8 => self.ins.tructions().push(vm::Instruction::Read64),
                sz => panic!("cannot read variable with size: {:?}", sz),
            }
        }
    }

    fn gen_trunc_type(&mut self, ty: &Type) {
        if let Type::Pointer(_) = ty {
        } else {
            match ty.sizeof() {
                1 => self.ins.tructions().push(vm::Instruction::Trunc8),
                2 => self.ins.tructions().push(vm::Instruction::Trunc16),
                4 => self.ins.tructions().push(vm::Instruction::Trunc32),
                _ => {},
            }
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
        let basety = Type::from_specifier(self, tys);
        let mut offset = if let Some(l) = self.block_scopes.last() {
            l.offset
        } else {
            self.globals.offset
        };
        let entries: Vec<(String, u64, Type, Option<ast::Initializer>)> = d.declarators.into_iter().map(|n| {
            let (nm, ty) = extract_declarator(&n.node.declarator.node, &basety);
            let oi = n.node.initializer.map(|i| i.node);
            let sz = ty.sizeof();
            let ret = (nm, offset, ty, oi);
            offset += sz;
            ret
        }).collect();
        let (scope, base, init) = if let Some(l) = self.block_scopes.last_mut() {
            (l, vm::Instruction::LocalAddr, false)
        } else {
            (&mut self.globals, vm::Instruction::GlobalAddr, true)
        };
        scope.offset = offset;
        if let ast::DeclarationSpecifier::StorageClass(s) = &d.specifiers[0].node {
            match s.node {
                ast::StorageClassSpecifier::Typedef => {
                    for (nm, _, ty, _) in entries {
                        self.typedefs.insert(nm.clone(), ty.clone());
                    }
                    return;
                },
                _ => {}
            }
        }
        for (nm, off, ty, _oi) in &entries {
            scope.entries.insert(nm.clone(), Entry { offset: *off, ty: ty.clone() });
        }
        self.ins.emit_init = init;
        for (_nm, off, ty, oi) in entries {
            if let Some(i) = oi {
                self.compile_initializer(ty, base.clone(), off, i);
            }
        }
        self.ins.emit_init = false;
    }

    fn compile_initializer(&mut self, ty: Type, base: vm::Instruction, off: u64, i: ast::Initializer) {
        match i {
            ast::Initializer::Expression(exp) => {
                self.ins.tructions().push(base);
                self.ins.tructions().push(vm::Instruction::Lit64(off));
                self.ins.tructions().push(vm::Instruction::Add);
                self.compile_expression(exp.node.clone());
                self.gen_trunc_type(&ty);
                self.ins.tructions().push(vm::Instruction::Write);
            },
            ast::Initializer::List(il) => {
                match ty {
                    Type::Array(_, aty) => {
                        let sz = aty.sizeof();
                        let mut o = off;
                        for i in il {
                            self.compile_initializer(*aty.clone(), base.clone(), o, i.node.initializer.node);
                            o += sz;
                        }
                    }
                    _ => panic!("list initializer for invalid type"),
                }
            },
        }
    }

    fn compile_definition(&mut self, d: ast::FunctionDefinition) {
        let pc = self.pc();
        let mut mtys = None;
        for s in d.specifiers.iter() {
            if let ast::DeclarationSpecifier::TypeSpecifier(t) = &s.node {
                mtys = Some(&t.node);
                break;
            }
        }
        let tys = mtys.expect("failed to find return type in function definition");
        let basety = Type::from_specifier(self, tys);
        let (nm, ret) = extract_declarator(&d.declarator.node, &basety);
        self.functions.insert(nm.clone(), Function {
            offset: pc,
            ret,
        });
        let mut offset = 0;
        let mut mfunc = None;
        for decl in d.declarator.node.derived.iter() {
            log::info!("node: {:?}", decl.node);
            if let ast::DerivedDeclarator::Function(f) = &decl.node {
                mfunc = Some(f);
            }
        }
        let params: Vec<(String, Entry)> = if let Some(f) = mfunc {
            f.node.parameters.iter().map(|n| {
                let decl = &n.node.declarator.as_ref().expect("missing parameter name").node;
                let basety = if let ast::DeclarationSpecifier::TypeSpecifier(t) = &n.node.specifiers[0].node {
                    Type::from_specifier(self, &t.node)
                } else {
                    panic!("non-type specifier found")
                };
                let (nm, ty) = extract_declarator(decl, &basety);
                let ret = (nm, Entry { offset, ty: ty.clone() });
                offset += ty.sizeof();
                ret
            }).collect()
        } else {
            Vec::new()
        };
        self.block_scopes.push(Scope { offset, entries: params.clone().into_iter().collect() });
        for (_, p) in params.iter() {
            if let ty@Type::Struct(_, _) = &p.ty {
                let mut offsets = Vec::new();
                ty.field_offsets(0, &mut offsets);
                for (off, _) in offsets.into_iter().rev() {
                    self.ins.tructions().push(vm::Instruction::LocalAddr);
                    self.ins.tructions().push(vm::Instruction::Lit64(p.offset + off));
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.ins.tructions().push(vm::Instruction::Swap);
                    self.ins.tructions().push(vm::Instruction::Write);
                }
            } else {
                self.ins.tructions().push(vm::Instruction::LocalAddr);
                self.ins.tructions().push(vm::Instruction::Lit64(p.offset));
                self.ins.tructions().push(vm::Instruction::Add);
                self.ins.tructions().push(vm::Instruction::Swap);
                self.ins.tructions().push(vm::Instruction::Write);
            }
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
                    let ty = self.compile_expression(n.node);
                    if ty != Type::Void {
                        self.ins.tructions().push(vm::Instruction::Dump);
                    }
                }
            },
            ast::Statement::Return(me) => {
                if let Some(e) = me {
                    self.compile_expression(e.node);
                }
                self.ins.tructions().push(vm::Instruction::Return);
            },
            ast::Statement::Break => {
                self.gen_break();
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
            },
            ast::Statement::For(f) => {
                let offset = if let Some(sc) = self.block_scopes.last() {
                    sc.offset
                } else {
                    0
                };
                self.block_scopes.push(Scope { offset, entries: HashMap::new() });
                match f.node.initializer.node {
                    ast::ForInitializer::Empty => {},
                    ast::ForInitializer::Expression(e) => {
                        self.compile_expression(e.node);
                    },
                    ast::ForInitializer::Declaration(d) => {
                        self.compile_declaration(d.node);
                    },
                    ast::ForInitializer::StaticAssert(_) => panic!("static assert in for loop"),
                }
                let start = self.ins.tructions().len() as u64;
                let sjmp = if let Some(c) = f.node.condition {
                    self.compile_expression(c.node);
                    self.ins.tructions().push(vm::Instruction::Not);
                    self.ins.tructions().push(vm::Instruction::Program);
                    let jmp = self.ins.tructions().len();
                    self.ins.tructions().push(vm::Instruction::Nop);
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.ins.tructions().push(vm::Instruction::Swap);
                    self.ins.tructions().push(vm::Instruction::JumpIf);
                    Some(jmp)
                } else { None };
                self.start_breakable();
                self.compile_statement(f.node.statement.node);
                if let Some(st) = f.node.step {
                    self.compile_expression(st.node);
                }
                self.ins.tructions().push(vm::Instruction::Program);
                let lit = self.literal(start);
                self.ins.tructions().push(lit);
                self.ins.tructions().push(vm::Instruction::Add);
                self.ins.tructions().push(vm::Instruction::Jump);
                let end = self.ins.tructions().len() as u64;
                if let Some(jmp) = sjmp {
                    self.ins.tructions()[jmp] = self.literal(end);
                }
                self.end_breakable(end);
                self.block_scopes.pop();
            },
            _ => panic!("unsupported statement: {:?}", d),
        }
    }

    // like compile_expression, but pushes an address to the stack rather than a value
    fn compile_expression_lvalue(&mut self, e: ast::Expression) -> Type {
        match e {
            ast::Expression::Identifier(i) => self.gen_push_var_addr(&i.node.name),
            ast::Expression::Member(me) => {
                let nm = me.node.identifier.node.name;
                if let Type::Struct(_, fields) = self.compile_expression(me.node.expression.node) {
                    if let Some(f) = fields.get(&nm) {
                        self.ins.tructions().push(vm::Instruction::Lit64(f.offset));
                        self.ins.tructions().push(vm::Instruction::Add);
                        f.ty.clone()
                    } else {
                        panic!("struct field does not exist: {}", nm);
                    }
                } else {
                    panic!("attempt to take member of non-struct");
                }
            },
            ast::Expression::UnaryOperator(uoe) => {
                match uoe.node.operator.node {
                    ast::UnaryOperator::Indirection => {
                        match self.compile_expression(uoe.node.operand.node) {
                            Type::Pointer(ty) => *ty,
                            Type::Array(_, ty) => *ty,
                            _ => {
                                panic!("attempted to dereference non-pointer expression in lvalue");
                            },
                        }
                    },
                    uop => panic!("unsupported unary operator in lvalue context: {:?}", uop),
                }
            },
            ast::Expression::BinaryOperator(boe) => {
                match boe.node.operator.node {
                    ast::BinaryOperator::Index => {
                        match self.compile_expression(boe.node.lhs.node) {
                            Type::Pointer(ty) | Type::Array(_, ty) => {
                                let sz = ty.sizeof();
                                self.compile_expression(boe.node.rhs.node);
                                self.ins.tructions().push(vm::Instruction::Lit64(sz));
                                self.ins.tructions().push(vm::Instruction::Mul);
                                self.ins.tructions().push(vm::Instruction::Add);
                                *ty
                            },
                            _ => {
                                panic!("attempt to dereference non-pointer type")
                            },
                        }
                    },
                    bop => panic!("unsupported binary operator in lvalue context: {:?}", bop),
                }
            },
            _ => {
                panic!("unknown lvalue!");
                // self.compile_expression(e);
                // Type::Int // TODO
            },
        }
    }

    // pushes a single result value to the stack
    fn compile_expression(&mut self, e: ast::Expression) -> Type {
        match e {
            ast::Expression::Constant(c) => match c.node {
                ast::Constant::Integer(i) => {
                    let val = i.number.parse().expect("failed to parse literal");
                    self.ins.tructions().push(vm::Instruction::Lit64(val));
                    Type::Long
                },
                ast::Constant::Character(c) => {
                    let val = c.chars().nth(1).expect("empty character literal");
                    self.ins.tructions().push(vm::Instruction::Lit8(val as u8));
                    Type::Char
                },
                co => panic!("unsupported literal: {:?}", co),
            },
            ast::Expression::StringLiteral(sl) => {
                let mut full = String::new();
                for bs in sl.node {
                    let s = bs.replace("\\n", "\n").replace("\\r", "\r").replace("\\t", "\t").replace("\\\\", "\\").replace("\\\"", "\"");
                    let mut cs = s.chars();
                    cs.next(); cs.next_back(); // remove quotes
                    full += cs.as_str()
                }
                full += "\0";
                self.ins.emit_init = true;
                let ret = self.globals.offset;
                for c in full.chars() {
                    self.ins.tructions().push(vm::Instruction::GlobalAddr);
                    self.ins.tructions().push(vm::Instruction::Lit64(self.globals.offset));
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.ins.tructions().push(vm::Instruction::Lit8(c as u8));
                    self.ins.tructions().push(vm::Instruction::Write);
                    self.globals.offset += 1;
                }
                self.ins.emit_init = false;
                self.ins.tructions().push(vm::Instruction::GlobalAddr);
                self.ins.tructions().push(vm::Instruction::Lit64(ret));
                self.ins.tructions().push(vm::Instruction::Add);
                Type::Pointer(Box::new(Type::Char))
            },
            ast::Expression::Identifier(i) => {
                let ty = self.gen_push_var_addr(&i.node.name);
                self.gen_read_type(&ty);
                ty.clone()
            },
            ast::Expression::Member(me) => {
                let nm = me.node.identifier.node.name;
                let ty = self.compile_expression(me.node.expression.node);
                if let Type::Struct(_, fields) = ty {
                    if let Some(f) = fields.get(&nm) {
                        self.ins.tructions().push(vm::Instruction::Lit64(f.offset));
                        self.ins.tructions().push(vm::Instruction::Add);
                        self.gen_read_type(&f.ty);
                        f.ty.clone()
                    } else {
                        panic!("struct field does not exist: {}", nm);
                    }
                } else {
                    panic!("attempt to take member of non-struct type: {:?}", ty);
                }
            },
            ast::Expression::Call(ce) => {
                for e in ce.node.arguments.into_iter().rev() {
                    if let ty@Type::Struct(_, _) = self.compile_expression(e.node) {
                        let mut offsets = Vec::new();
                        ty.field_offsets(0, &mut offsets);
                        for (off, ty) in offsets {
                            self.ins.tructions().push(vm::Instruction::Dup);
                            self.ins.tructions().push(vm::Instruction::Lit64(off));
                            self.ins.tructions().push(vm::Instruction::Add);
                            self.gen_read_type(&ty);
                            self.ins.tructions().push(vm::Instruction::Swap);
                        }
                        self.ins.tructions().push(vm::Instruction::Drop);
                    }
                }
                match &ce.node.callee.node {
                    ast::Expression::Identifier(i) if i.node.name == "syscall" => {
                        self.ins.tructions().push(vm::Instruction::Syscall);
                        Type::Void
                    },
                    _ => {
                        let ty = self.compile_expression_lvalue(ce.node.callee.node);
                        self.ins.tructions().push(vm::Instruction::Call);
                        if let Type::Function(ret) = &ty {
                            *ret.clone()
                        } else {
                            panic!("attempt to call non-function type");
                        }
                    }
                }
            },
            ast::Expression::UnaryOperator(uoe) => {
                match uoe.node.operator.node {
                    ast::UnaryOperator::Address => {
                        let ty = self.compile_expression_lvalue(uoe.node.operand.node);
                        Type::Pointer(Box::new(ty))
                    },
                    ast::UnaryOperator::Indirection => {
                        match self.compile_expression(uoe.node.operand.node) {
                            Type::Pointer(ty) => {
                                self.gen_read_type(&ty);
                                *ty
                            },
                            Type::Array(_, ty) => {
                                self.gen_read_type(&ty);
                                *ty
                            },
                            _ => {
                                panic!("attempted to dereference non-pointer expression");
                            },
                        }
                    },
                    uop => panic!("unsupported unary operator (with lvalue): {:?}", uop),
                }
            },
            ast::Expression::BinaryOperator(boe) => {
                if binop_has_lvalue(&boe.node.operator.node) {
                    let tl = self.compile_expression_lvalue(boe.node.lhs.node);
                    self.compile_expression(boe.node.rhs.node);
                    match boe.node.operator.node {
                        ast::BinaryOperator::Assign => {
                            self.gen_trunc_type(&tl);
                            self.ins.tructions().push(vm::Instruction::Dup);
                            self.ins.tructions().push(vm::Instruction::Rot);
                            self.ins.tructions().push(vm::Instruction::Write);
                            tl
                        },
                        ast::BinaryOperator::AssignPlus => {
                            self.ins.tructions().push(vm::Instruction::Swap);
                            self.ins.tructions().push(vm::Instruction::Dup);
                            self.gen_read_type(&tl);
                            self.ins.tructions().push(vm::Instruction::Rot);
                            self.ins.tructions().push(vm::Instruction::Rot);
                            self.ins.tructions().push(vm::Instruction::Add);
                            self.gen_trunc_type(&tl);
                            self.ins.tructions().push(vm::Instruction::Dup);
                            self.ins.tructions().push(vm::Instruction::Rot);
                            self.ins.tructions().push(vm::Instruction::Write);
                            tl
                        },
                        ast::BinaryOperator::Index => {
                            match tl {
                                Type::Pointer(ty) | Type::Array(_, ty) => {
                                    let sz = ty.sizeof();
                                    self.ins.tructions().push(vm::Instruction::Lit64(sz));
                                    self.ins.tructions().push(vm::Instruction::Mul);
                                    self.ins.tructions().push(vm::Instruction::Add);
                                    self.gen_read_type(&ty);
                                    *ty
                                },
                                _ => panic!("attempted to index non-pointer"),
                            }
                        },
                        bop => panic!("unsupported binary operator (with lvalue): {:?}", bop),
                    }
                } else {
                    let tl = self.compile_expression(boe.node.lhs.node);
                    let tr = self.compile_expression(boe.node.rhs.node);
                    match (&tl, &tr) {
                        (Type::Pointer(pty), _)
                            | (Type::Array(_, pty), _)
                            | (_, Type::Pointer(pty))
                            | (_, Type::Array(_, pty)) => {
                                let sz = pty.sizeof();
                                self.ins.tructions().push(vm::Instruction::Lit64(sz));
                                self.ins.tructions().push(vm::Instruction::Mul);
                            },
                        _ => {},
                    }
                    match boe.node.operator.node {
                        ast::BinaryOperator::Plus => self.ins.tructions().push(vm::Instruction::Add),
                        ast::BinaryOperator::Minus => self.ins.tructions().push(vm::Instruction::Sub),
                        ast::BinaryOperator::Multiply => self.ins.tructions().push(vm::Instruction::Mul),
                        ast::BinaryOperator::Less => self.ins.tructions().push(vm::Instruction::Less),
                        ast::BinaryOperator::Greater => {
                            self.ins.tructions().push(vm::Instruction::Swap);
                            self.ins.tructions().push(vm::Instruction::Less);
                        },
                        bop => panic!("unsupported binary operator (no lvalue): {:?}", bop),
                    }
                    tl // TODO: actually pick the right type instead of The Left One

                }
            },
            _ => panic!("unsupported expression: {:?}", e),
        }
    }
}
