pub mod debug;

use crate::vm;

use teleia::*;

use std::collections::HashMap;
use lang_c::ast as ast;
use lang_c::span::Node;

#[derive(Debug, Clone)]
pub enum LinkError {
    NoMainFunction,
}
impl std::error::Error for LinkError {}
impl std::fmt::Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoMainFunction => write!(f, "no main function"),
        }
    }
}

pub struct ErrorContext<'a> {
    src: &'a str,
    sort: &'static str,
    span: lang_c::span::Span,
}
impl<'a> ErrorContext<'a> {
    pub fn err(&self, kind: ErrorKind) -> Error {
        let (lst, _) = lang_c::loc::get_location_for_offset(self.src, self.span.start);
        let (len, _) = lang_c::loc::get_location_for_offset(self.src, self.span.end);
        Error {
            kind,
            start: lst.line as u64,
            end: len.line as u64,
        }
    }
    pub fn erm<A>(&self, kind: ErrorKind) -> Erm<A> {
        Err(self.err(kind).into())
    }
}
trait WithContext {
    type Inside;
    fn with_context<F, A>(&self, t: &'static str, ec: &ErrorContext, f: F) -> Erm<A> where F: FnMut(ErrorContext, &Self::Inside) -> Erm<A>;
}
impl<X> WithContext for Node<X> {
    type Inside = X;
    fn with_context<F, A>(&self, t: &'static str, ec: &ErrorContext, mut f: F) -> Erm<A> where F: FnMut(ErrorContext, &Self::Inside) -> Erm<A> {
        let new = ErrorContext { src: ec.src, sort: t, span: self.span };
        let (lst, _) = lang_c::loc::get_location_for_offset(ec.src, ec.span.start);
        let (len, _) = lang_c::loc::get_location_for_offset(ec.src, ec.span.end);
        let msg = if lst.line == len.line {
            format!("while compiling {} at line {}", ec.sort, lst.line)
        } else {
            format!("while compiling {} from line {} to line {}", ec.sort, lst.line, len.line)
        };
        if ec.sort == "translation unit" {
            f(new, &self.node)
        } else {
            f(new, &self.node).wrap_err(msg)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error {
    kind: ErrorKind,
    start: u64,
    end: u64,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.start == self.end {
            write!(f, "compile error at line {}: {}", self.start, self.kind)
        } else {
            write!(f, "compile error from line {} to line {}: {}", self.start, self.end, self.kind)
        }
    }
}
impl std::error::Error for Error {}

#[derive(Debug, Clone)]
pub enum ErrorKind {
    Unimplemented(String),
    UnboundVariable(String),
    UnboundTypedef(String),
    DeclaratorHasNoIdentifier,
    MalformedLiteral(String),
    MalformedStructType(ast::StructType),
    ArrayTypeMissingSize,
    ArraySizeExpressionNotConstant,
    ArraySizeConstantNotInteger,
    BreakOutsideLoop,
    BreakableStackUnderflow,
    UnsureHowToRead(Type),
    UnsupportedStaticAssert,
    ListInitializerForInvalidType(Type),
    MissingStructField(String),
    MemberOfNonStruct(Type),
    IndexOfNonArray(Type),
    DereferenceOfNonPointer(Type),
    CallOfNonFunction(Type),
    MissingReturnType,
    MissingParameterName,
}
impl std::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unimplemented(s) => write!(f, "unimplemented {s:}"),
            Self::UnboundVariable(nm) => write!(f, "unbound variable: {nm:}"),
            Self::UnboundTypedef(nm) => write!(f, "unbound typedef: {nm:}"),
            Self::DeclaratorHasNoIdentifier => write!(f, "declarator has no identifier"),
            Self::MalformedLiteral(l) => write!(f, "malformed literal: {l:?}"),
            Self::MalformedStructType(st) => write!(f, "malformed struct type: {st:?}"),
            Self::ArrayTypeMissingSize => write!(f, "array type does not have size"),
            Self::ArraySizeExpressionNotConstant => write!(f, "array size expression is not constant"),
            Self::ArraySizeConstantNotInteger => write!(f, "array size constant is not an integer"),
            Self::BreakOutsideLoop => write!(f, "attempted to break outside loop/switch"),
            Self::BreakableStackUnderflow => write!(f, "breakable stack underflow"),
            Self::UnsureHowToRead(ty) => write!(f, "unsure how to read type: {ty:?}"),
            Self::UnsupportedStaticAssert => write!(f, "static assertions are not supported"),
            Self::ListInitializerForInvalidType(ty) => write!(f, "list initializer for invalid type: {ty:?}"),
            Self::MissingStructField(nm) => write!(f, "missing struct field: {nm:}"),
            Self::MemberOfNonStruct(ty) => write!(f, "attempted to take member of non-struct type: {ty:?}"),
            Self::IndexOfNonArray(ty) => write!(f, "attempted to index non-array type: {ty:?}"),
            Self::DereferenceOfNonPointer(ty) => write!(f, "attempted to dereference non-pointer type: {ty:?}"),
            Self::CallOfNonFunction(ty) => write!(f, "attempted to call non-function type: {ty:?}"),
            Self::MissingReturnType => write!(f, "could not find return type"),
            Self::MissingParameterName => write!(f, "could not find parameter name"),
        }
    }
}

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
    pub fn from_specifier(vm: &mut State, ec: &ErrorContext, spec: &lang_c::ast::TypeSpecifier) -> Erm<Self> {
        match spec {
            ast::TypeSpecifier::Void => Ok(Self::Void),
            ast::TypeSpecifier::Char => Ok(Self::Char),
            ast::TypeSpecifier::Short => Ok(Self::Short),
            ast::TypeSpecifier::Int => Ok(Self::Int),
            ast::TypeSpecifier::Long => Ok(Self::Long),
            ast::TypeSpecifier::Float => Ok(Self::Float),
            ast::TypeSpecifier::Double => Ok(Self::Double),
            ast::TypeSpecifier::Signed => Ok(Self::Signed),
            ast::TypeSpecifier::Unsigned => Ok(Self::Unsigned),
            ast::TypeSpecifier::Bool => Ok(Self::Bool),
            ast::TypeSpecifier::TypedefName(nm) =>
                Ok(vm.typedefs.get(&nm.node.name)
                   .ok_or(ec.err(ErrorKind::UnboundTypedef(nm.node.name.clone())))?
                   .clone()),
            ast::TypeSpecifier::Struct(s) => vm.handle_struct_def(ec, &s.node),
            _ => ec.erm(ErrorKind::Unimplemented(format!("from_specifier for {spec:?}"))),
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

fn extract_declarationspecifier(vm: &mut State, ec: &ErrorContext, d: &[Node<ast::DeclarationSpecifier>]) -> Erm<Type> {
    let mut mtys = None;
    for s in d.iter() {
        if let ast::DeclarationSpecifier::TypeSpecifier(t) = &s.node {
            mtys = Some(&t.node);
            break;
        }
    }
    let tys = mtys.ok_or(ec.err(ErrorKind::MissingReturnType))?;
    Type::from_specifier(vm, ec, tys)
}

fn extract_specifierqualifier(vm: &mut State, ec: &ErrorContext, d: &[Node<ast::SpecifierQualifier>]) -> Erm<Type> {
    let mut mtys = None;
    for s in d.iter() {
        if let ast::SpecifierQualifier::TypeSpecifier(t) = &s.node {
            mtys = Some(&t.node);
            break;
        }
    }
    let tys = mtys.ok_or(ec.err(ErrorKind::MissingReturnType))?;
    Type::from_specifier(vm, ec, tys)
}

fn extract_declarator(ec: &ErrorContext, d: &ast::Declarator, base: &Type) -> Erm<(String, Type)> {
    let nm = d.kind.with_context("declarator", ec, |ec, node| {
        if let ast::DeclaratorKind::Identifier(i) = node {
            Ok(i.node.name.clone())
        } else {
            ec.erm(ErrorKind::DeclaratorHasNoIdentifier)
        }
    })?;
    let mut ty = base.clone();
    for x in &d.derived {
        x.with_context("derived declarator", ec, |ec, node| {
            match node {
                ast::DerivedDeclarator::Pointer(_) => {
                    ty = Type::Pointer(Box::new(ty.clone()));
                    Ok(())
                },
                ast::DerivedDeclarator::Array(l) => {
                    l.with_context("array type size", &ec, |ec, node| {
                        if let ast::ArraySize::VariableExpression(bve) = &node.size {
                            if let ast::Expression::Constant(c) = &bve.node {
                                if let ast::Constant::Integer(i) = &c.node {
                                    let len = i.number.parse()?;
                                    ty = Type::Array(len, Box::new(ty.clone()));
                                    Ok(())
                                } else { ec.erm(ErrorKind::ArraySizeConstantNotInteger) }
                            } else { ec.erm(ErrorKind::ArraySizeExpressionNotConstant) }
                        } else { ec.erm(ErrorKind::ArrayTypeMissingSize) }
                    })
                },
                _ => Ok(()),
            }
        })?;
    }
    Ok((nm, ty))
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

    pub fn finalize(&self) -> Erm<(u64, Vec<vm::Instruction>)> {
        let main = self.functions.get("main").ok_or(LinkError::NoMainFunction)?;
        let entry = self.ins.instructions.len();
        let mut ins = self.ins.instructions.clone();
        ins.append(&mut self.ins.instructions_init.clone());
        ins.push(vm::Instruction::Program);
        ins.push(vm::Instruction::Lit64(main.offset));
        ins.push(vm::Instruction::Add);
        ins.push(vm::Instruction::Call);
        Ok((entry as _, ins))
    }

    pub fn load(&mut self, path: &str) -> Erm<()> {
        let config = lang_c::driver::Config::default();
        let parse = lang_c::driver::parse(&config, path)?;
        let ec = ErrorContext {
            src: &parse.source,
            sort: "translation unit",
            span: lang_c::span::Span { start: 0, end: 0 },
        };
        self.compile_translation_unit(&ec, parse.unit)?;
        Ok(())
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

    fn handle_struct_def(&mut self, ec: &ErrorContext, st: &ast::StructType) -> Erm<Type> {
        let names = match st.kind.node {
            ast::StructKind::Struct => &mut self.structs,
            ast::StructKind::Union => &mut self.unions,
        };
        let snm = st.identifier.as_ref().map(|nid| nid.node.name.clone());
        if let Some(nm) = &snm {
            if let Some(t) = names.get(nm) {
                return Ok(t.clone());
            }
        }
        if let Some(decls) = &st.declarations {
            let mut fields = HashMap::new();
            let mut offset = 0;
            let mut totalsz = 0;
            for d in decls {
                if let ast::StructDeclaration::Field(df) = &d.node {
                    let base = extract_specifierqualifier(self, ec, &df.node.specifiers)?;
                    for sdecl in df.node.declarators.iter() {
                        if let Some(decl) = &sdecl.node.declarator {
                            let (nm, ty) = extract_declarator(ec, &decl.node, &base)?;
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
                    Ok(ty)
                },
                ast::StructKind::Union => {
                    let ty = Type::Union(totalsz, fields);
                    if let Some(nm) = snm { self.unions.insert(nm, ty.clone()); }
                    Ok(ty)
                },
            };
        }
        ec.erm(ErrorKind::MalformedStructType(st.clone()))
    }

    fn start_breakable(&mut self) {
        self.breakables.push(Breakable {
            breaks: Vec::new(),
        });
    }

    fn gen_break(&mut self, ec: &ErrorContext) -> Erm<()> {
        let Some(br) = self.breakables.last_mut() else {
            return ec.erm(ErrorKind::BreakOutsideLoop);
        };
        self.ins.tructions().push(vm::Instruction::Program);
        let nop = self.ins.tructions().len();
        self.ins.tructions().push(vm::Instruction::Nop);
        self.ins.tructions().push(vm::Instruction::Add);
        self.ins.tructions().push(vm::Instruction::Jump);
        br.breaks.push(nop as _);
        Ok(())
    }

    fn end_breakable(&mut self, ec: &ErrorContext, end: u64) -> Erm<()> {
        let Some(br) = self.breakables.pop() else {
            return ec.erm(ErrorKind::BreakableStackUnderflow);
        };
        for i in br.breaks {
            self.ins.tructions()[i as usize] = self.literal(end);
        }
        Ok(())
    }

    fn gen_push_var_addr(&mut self, ec: &ErrorContext, nm: &str) -> Erm<Type> {
        for sc in &self.block_scopes {
            if let Some(e) = sc.entries.get(nm) {
                self.ins.tructions().push(vm::Instruction::LocalAddr);
                self.ins.tructions().push(vm::Instruction::Lit64(e.offset));
                self.ins.tructions().push(vm::Instruction::Add);
                return Ok(e.ty.clone());
            }
        }
        if let Some(e) = self.globals.entries.get(nm) {
            self.ins.tructions().push(vm::Instruction::GlobalAddr);
            self.ins.tructions().push(vm::Instruction::Lit64(e.offset));
            self.ins.tructions().push(vm::Instruction::Add);
            return Ok(e.ty.clone());
        }
        if let Some(f) = self.functions.get(nm) {
            self.ins.tructions().push(vm::Instruction::Program);
            self.ins.tructions().push(vm::Instruction::Lit64(f.offset));
            self.ins.tructions().push(vm::Instruction::Add);
            return Ok(Type::Function(Box::new(f.ret.clone())));
        }
        ec.erm(ErrorKind::UnboundVariable(nm.to_string()))
    }

    fn gen_read_type(&mut self, ec: &ErrorContext, ty: &Type) -> Erm<()> {
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
                _ => return ec.erm(ErrorKind::UnsureHowToRead(ty.clone())),
            }
        }
        Ok(())
    }

    fn gen_trunc_type(&mut self, ty: &Type) -> Erm<()> {
        if let Type::Pointer(_) = ty {
        } else {
            match ty.sizeof() {
                1 => self.ins.tructions().push(vm::Instruction::Trunc8),
                2 => self.ins.tructions().push(vm::Instruction::Trunc16),
                4 => self.ins.tructions().push(vm::Instruction::Trunc32),
                _ => {},
            }
        }
        Ok(())
    }

    fn compile_translation_unit(&mut self, ec: &ErrorContext, tu: ast::TranslationUnit) -> Erm<()> {
        for n in tu.0 {
            self.compile_external_declaration(ec, &n)?;
        }
        Ok(())
    }

    fn compile_external_declaration(&mut self, ec: &ErrorContext, ned: &Node<ast::ExternalDeclaration>) -> Erm<()> {
        ned.with_context("external declaration", ec, |ec, ed| {
            match ed {
                ast::ExternalDeclaration::Declaration(n) => self.compile_declaration(&ec, n)?,
                ast::ExternalDeclaration::FunctionDefinition(d) => self.compile_definition(&ec, d)?,
                _ => return ec.erm(ErrorKind::UnsupportedStaticAssert),
            }
            Ok(())
        })
    }

    fn compile_declaration(&mut self, ec: &ErrorContext, nd: &Node<ast::Declaration>) -> Erm<()> {
        nd.with_context("declaration", ec, |ec, d| {
            let basety = extract_declarationspecifier(self, &ec, &d.specifiers)?;
            let mut offset = if let Some(l) = self.block_scopes.last() {
                l.offset
            } else {
                self.globals.offset
            };
            let entries: Vec<(String, u64, Type, Option<&Node<ast::Initializer>>)> = d.declarators.iter().map(|n| {
                let (nm, ty) = extract_declarator(&ec, &n.node.declarator.node, &basety)?;
                let oi = n.node.initializer.as_ref();
                let sz = ty.sizeof();
                let ret = (nm, offset, ty, oi);
                offset += sz;
                Ok(ret)
            }).collect::<Erm<Vec<_>>>()?;
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
                        return Ok(());
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
                    self.compile_initializer(&ec, ty, base.clone(), off, i)?;
                }
            }
            self.ins.emit_init = false;
            Ok(())
        })
    }

    fn compile_initializer(&mut self, ec: &ErrorContext, ty: Type, base: vm::Instruction, off: u64, ni: &Node<ast::Initializer>) -> Erm<()> {
        ni.with_context("initializer", ec, |ec, i| {
            match i {
                ast::Initializer::Expression(exp) => {
                    self.ins.tructions().push(base.clone());
                    self.ins.tructions().push(vm::Instruction::Lit64(off));
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.compile_expression(&ec, &exp)?;
                    self.gen_trunc_type(&ty)?;
                    self.ins.tructions().push(vm::Instruction::Write);
                },
                ast::Initializer::List(il) => {
                    match &ty {
                        Type::Array(_, aty) => {
                            let sz = aty.sizeof();
                            let mut o = off;
                            for i in il {
                                self.compile_initializer(&ec, *aty.clone(), base.clone(), o, &i.node.initializer)?;
                                o += sz;
                            }
                        }
                        _ => return ec.erm(ErrorKind::ListInitializerForInvalidType(ty.clone())),
                    }
                },
            }
            Ok(())
        })
    }

    fn compile_definition(&mut self, ec: &ErrorContext, nd: &Node<ast::FunctionDefinition>) -> Erm<()> {
        nd.with_context("definition", ec, |ec, d| {
            let pc = self.pc();
            let basety = extract_declarationspecifier(self, &ec, &d.specifiers)?;
            let (nm, ret) = extract_declarator(&ec, &d.declarator.node, &basety)?;
            self.functions.insert(nm.clone(), Function {
                offset: pc,
                ret,
            });
            let mut offset = 0;
            let mut mfunc = None;
            for decl in d.declarator.node.derived.iter() {
                if let ast::DerivedDeclarator::Function(f) = &decl.node {
                    mfunc = Some(f);
                }
            }
            let params: Vec<(String, Entry)> = if let Some(f) = mfunc {
                f.node.parameters.iter().map(|n| {
                    let decl = &n.node.declarator.as_ref().ok_or(ec.err(ErrorKind::MissingParameterName))?.node;
                    let basety = extract_declarationspecifier(self, &ec, &n.node.specifiers)?;
                    let (nm, ty) = extract_declarator(&ec, decl, &basety)?;
                    let ret = (nm, Entry { offset, ty: ty.clone() });
                    offset += ty.sizeof();
                    Ok(ret)
                }).collect::<Erm<Vec<_>>>()?
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
            self.compile_statement(&ec, &d.statement)?;
            self.block_scopes.pop();
            self.ins.tructions().push(vm::Instruction::Return);
            Ok(())
        })
    }

    // neither produces or consumes stack
    fn compile_statement(&mut self, ec: &ErrorContext, nd: &Node<ast::Statement>) -> Erm<()> {
        nd.with_context("statement", ec, |ec, d| {
            match d {
                ast::Statement::Expression(mn) => {
                    if let Some(n) = mn {
                        let ty = self.compile_expression(&ec, &n)?;
                        if ty != Type::Void {
                            self.ins.tructions().push(vm::Instruction::Dump);
                        }
                    }
                },
                ast::Statement::Return(me) => {
                    if let Some(e) = me {
                        self.compile_expression(&ec, &e)?;
                    }
                    self.ins.tructions().push(vm::Instruction::Return);
                },
                ast::Statement::Break => {
                    self.gen_break(&ec)?;
                },
                ast::Statement::Compound(nodes) => {
                    let offset = if let Some(sc) = self.block_scopes.last() {
                        sc.offset
                    } else {
                        0
                    };
                    self.block_scopes.push(Scope { offset, entries: HashMap::new() });
                    for n in nodes {
                        match &n.node {
                            ast::BlockItem::Statement(s) => self.compile_statement(&ec, &s)?,
                            ast::BlockItem::Declaration(d) => self.compile_declaration(&ec, &d)?,
                            ast::BlockItem::StaticAssert(_) => return ec.erm(ErrorKind::UnsupportedStaticAssert),
                        }
                    }
                    self.block_scopes.pop();
                },
                ast::Statement::If(i) => {
                    self.compile_expression(&ec, &i.node.condition)?;
                    self.ins.tructions().push(vm::Instruction::Not);
                    self.ins.tructions().push(vm::Instruction::Program);
                    let jmp = self.ins.tructions().len();
                    self.ins.tructions().push(vm::Instruction::Nop);
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.ins.tructions().push(vm::Instruction::Swap);
                    self.ins.tructions().push(vm::Instruction::JumpIf);
                    self.compile_statement(&ec, &i.node.then_statement)?;
                    self.ins.tructions().push(vm::Instruction::Program);
                    let endjmp = self.ins.tructions().len();
                    self.ins.tructions().push(vm::Instruction::Nop);
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.ins.tructions().push(vm::Instruction::Jump);
                    let here = self.ins.tructions().len();
                    self.ins.tructions()[jmp] = self.literal(here as _);
                    if let Some(els) = &i.node.else_statement {
                        self.compile_statement(&ec, &els)?;
                    }
                    let here = self.ins.tructions().len();
                    self.ins.tructions()[endjmp] = self.literal(here as _);
                },
                ast::Statement::While(w) => {
                    let start = self.ins.tructions().len() as u64;
                    self.compile_expression(&ec, &w.node.expression)?;
                    self.ins.tructions().push(vm::Instruction::Not);
                    self.ins.tructions().push(vm::Instruction::Program);
                    let jmp = self.ins.tructions().len();
                    self.ins.tructions().push(vm::Instruction::Nop);
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.ins.tructions().push(vm::Instruction::Swap);
                    self.ins.tructions().push(vm::Instruction::JumpIf);
                    self.start_breakable();
                    self.compile_statement(&ec, &w.node.statement)?;
                    self.ins.tructions().push(vm::Instruction::Program);
                    let lit = self.literal(start);
                    self.ins.tructions().push(lit);
                    self.ins.tructions().push(vm::Instruction::Add);
                    self.ins.tructions().push(vm::Instruction::Jump);
                    let end = self.ins.tructions().len() as u64;
                    self.ins.tructions()[jmp] = self.literal(end);
                    self.end_breakable(&ec, end)?;
                },
                ast::Statement::For(f) => {
                    let offset = if let Some(sc) = self.block_scopes.last() {
                        sc.offset
                    } else {
                        0
                    };
                    self.block_scopes.push(Scope { offset, entries: HashMap::new() });
                    match &f.node.initializer.node {
                        ast::ForInitializer::Empty => {},
                        ast::ForInitializer::Expression(e) => {
                            self.compile_expression(&ec, &e)?;
                        },
                        ast::ForInitializer::Declaration(d) => {
                            self.compile_declaration(&ec, &d)?;
                        },
                        ast::ForInitializer::StaticAssert(_) => return ec.erm(ErrorKind::UnsupportedStaticAssert),
                    }
                    let start = self.ins.tructions().len() as u64;
                    let sjmp = if let Some(c) = &f.node.condition {
                        self.compile_expression(&ec, &c)?;
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
                    self.compile_statement(&ec, &f.node.statement)?;
                    if let Some(st) = &f.node.step {
                        self.compile_expression(&ec, &st)?;
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
                    self.end_breakable(&ec, end)?;
                    self.block_scopes.pop();
                },
                _ => return ec.erm(ErrorKind::Unimplemented(format!("statement: {:?}", d))),
            }
            Ok(())
        })
    }

    // like compile_expression, but pushes an address to the stack rather than a value
    fn compile_expression_lvalue(&mut self, ec: &ErrorContext, ne: &Node<ast::Expression>) -> Erm<Type> {
        ne.with_context("expression (lvalue)", ec, |ec, e| {
            match e {
                ast::Expression::Identifier(i) => self.gen_push_var_addr(&ec, &i.node.name),
                ast::Expression::Member(me) => {
                    let nm = me.node.identifier.node.name.clone();
                    let ty = self.compile_expression(&ec, &me.node.expression)?;
                    if let Type::Struct(_, fields) = &ty {
                        if let Some(f) = fields.get(&nm) {
                            self.ins.tructions().push(vm::Instruction::Lit64(f.offset));
                            self.ins.tructions().push(vm::Instruction::Add);
                            Ok(f.ty.clone())
                        } else {
                            ec.erm(ErrorKind::MissingStructField(nm))
                        }
                    } else {
                        ec.erm(ErrorKind::MemberOfNonStruct(ty.clone()))
                    }
                },
                ast::Expression::UnaryOperator(uoe) => {
                    match &uoe.node.operator.node {
                        ast::UnaryOperator::Indirection => {
                            match self.compile_expression(&ec, &uoe.node.operand)? {
                                Type::Pointer(ty) => Ok(*ty),
                                Type::Array(_, ty) => Ok(*ty),
                                ty => ec.erm(ErrorKind::DereferenceOfNonPointer(ty.clone())),
                            }
                        },
                        uop => return ec.erm(ErrorKind::Unimplemented(format!("unary operator lvalue: {:?}", uop))),
                    }
                },
                ast::Expression::BinaryOperator(boe) => {
                    match &boe.node.operator.node {
                        ast::BinaryOperator::Index => {
                            match self.compile_expression(&ec, &boe.node.lhs)? {
                                Type::Pointer(ty) | Type::Array(_, ty) => {
                                    let sz = ty.sizeof();
                                    self.compile_expression(&ec, &boe.node.rhs)?;
                                    self.ins.tructions().push(vm::Instruction::Lit64(sz));
                                    self.ins.tructions().push(vm::Instruction::Mul);
                                    self.ins.tructions().push(vm::Instruction::Add);
                                    Ok(*ty)
                                },
                                ty => ec.erm(ErrorKind::IndexOfNonArray(ty.clone())),
                            }
                        },
                        bop => return ec.erm(ErrorKind::Unimplemented(format!("binary operator lvalue: {:?}", bop)))
                    }
                },
                _ => return ec.erm(ErrorKind::Unimplemented(format!("lvalue: {:?}", e))),
            }
        })
    }

    // pushes a single result value to the stack
    fn compile_expression(&mut self, ec: &ErrorContext, ne: &Node<ast::Expression>) -> Erm<Type> {
        ne.with_context("expression (lvalue)", ec, |ec, e| {
            match e {
                ast::Expression::Constant(c) => match &c.node {
                    ast::Constant::Integer(i) => {
                        let val = i.number.parse()?;
                        self.ins.tructions().push(vm::Instruction::Lit64(val));
                        Ok(Type::Long)
                    },
                    ast::Constant::Character(c) => {
                        let val = c.chars().nth(1).ok_or(ec.err(ErrorKind::MalformedLiteral(c.clone())))?;
                        self.ins.tructions().push(vm::Instruction::Lit8(val as u8));
                        Ok(Type::Char)
                    },
                    co => return ec.erm(ErrorKind::Unimplemented(format!("literal: {:?}", co))),
                },
                ast::Expression::StringLiteral(sl) => {
                    let mut full = String::new();
                    for bs in &sl.node {
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
                    Ok(Type::Pointer(Box::new(Type::Char)))
                },
                ast::Expression::Identifier(i) => {
                    let ty = self.gen_push_var_addr(&ec, &i.node.name)?;
                    self.gen_read_type(&ec, &ty)?;
                    Ok(ty.clone())
                },
                ast::Expression::Member(me) => {
                    let nm = me.node.identifier.node.name.clone();
                    let ty = self.compile_expression(&ec, &me.node.expression)?;
                    if let Type::Struct(_, fields) = ty {
                        if let Some(f) = fields.get(&nm) {
                            self.ins.tructions().push(vm::Instruction::Lit64(f.offset));
                            self.ins.tructions().push(vm::Instruction::Add);
                            self.gen_read_type(&ec, &f.ty)?;
                            Ok(f.ty.clone())
                        } else {
                            ec.erm(ErrorKind::MissingStructField(nm))
                        }
                    } else {
                        ec.erm(ErrorKind::MemberOfNonStruct(ty))
                    }
                },
                ast::Expression::Call(ce) => {
                    for e in ce.node.arguments.iter().rev() {
                        if let ty@Type::Struct(_, _) = self.compile_expression(&ec, &e)? {
                            let mut offsets = Vec::new();
                            ty.field_offsets(0, &mut offsets);
                            for (off, ty) in offsets {
                                self.ins.tructions().push(vm::Instruction::Dup);
                                self.ins.tructions().push(vm::Instruction::Lit64(off));
                                self.ins.tructions().push(vm::Instruction::Add);
                                self.gen_read_type(&ec, &ty)?;
                                self.ins.tructions().push(vm::Instruction::Swap);
                            }
                            self.ins.tructions().push(vm::Instruction::Drop);
                        }
                    }
                    match &ce.node.callee.node {
                        ast::Expression::Identifier(i) if i.node.name == "syscall" => {
                            self.ins.tructions().push(vm::Instruction::Syscall);
                            Ok(Type::Void)
                        },
                        _ => {
                            let ty = self.compile_expression_lvalue(&ec, &ce.node.callee)?;
                            self.ins.tructions().push(vm::Instruction::Call);
                            if let Type::Function(ret) = &ty {
                                Ok(*ret.clone())
                            } else {
                                ec.erm(ErrorKind::CallOfNonFunction(ty))
                            }
                        }
                    }
                },
                ast::Expression::UnaryOperator(uoe) => {
                    match &uoe.node.operator.node {
                        ast::UnaryOperator::Address => {
                            let ty = self.compile_expression_lvalue(&ec, &uoe.node.operand)?;
                            Ok(Type::Pointer(Box::new(ty)))
                        },
                        ast::UnaryOperator::Indirection => {
                            match self.compile_expression(&ec, &uoe.node.operand)? {
                                Type::Pointer(ty) => {
                                    self.gen_read_type(&ec, &ty)?;
                                    Ok(*ty)
                                },
                                Type::Array(_, ty) => {
                                    self.gen_read_type(&ec, &ty)?;
                                    Ok(*ty)
                                },
                                ty => ec.erm(ErrorKind::DereferenceOfNonPointer(ty)),
                            }
                        },
                        uop => return ec.erm(ErrorKind::Unimplemented(format!("unary operator: {:?}", uop))),
                    }
                },
                ast::Expression::BinaryOperator(boe) => {
                    if binop_has_lvalue(&boe.node.operator.node) {
                        let tl = self.compile_expression_lvalue(&ec, &boe.node.lhs)?;
                        self.compile_expression(&ec, &boe.node.rhs)?;
                        match &boe.node.operator.node {
                            ast::BinaryOperator::Assign => {
                                self.gen_trunc_type(&tl)?;
                                self.ins.tructions().push(vm::Instruction::Dup);
                                self.ins.tructions().push(vm::Instruction::Rot);
                                self.ins.tructions().push(vm::Instruction::Write);
                                Ok(tl)
                            },
                            ast::BinaryOperator::AssignPlus => {
                                self.ins.tructions().push(vm::Instruction::Swap);
                                self.ins.tructions().push(vm::Instruction::Dup);
                                self.gen_read_type(&ec, &tl)?;
                                self.ins.tructions().push(vm::Instruction::Rot);
                                self.ins.tructions().push(vm::Instruction::Rot);
                                self.ins.tructions().push(vm::Instruction::Add);
                                self.gen_trunc_type(&tl)?;
                                self.ins.tructions().push(vm::Instruction::Dup);
                                self.ins.tructions().push(vm::Instruction::Rot);
                                self.ins.tructions().push(vm::Instruction::Write);
                                Ok(tl)
                            },
                            ast::BinaryOperator::Index => {
                                match tl {
                                    Type::Pointer(ty) | Type::Array(_, ty) => {
                                        let sz = ty.sizeof();
                                        self.ins.tructions().push(vm::Instruction::Lit64(sz));
                                        self.ins.tructions().push(vm::Instruction::Mul);
                                        self.ins.tructions().push(vm::Instruction::Add);
                                        self.gen_read_type(&ec, &ty)?;
                                        Ok(*ty)
                                    },
                                    ty => ec.erm(ErrorKind::IndexOfNonArray(ty)),
                                }
                            },
                            bop => return ec.erm(ErrorKind::Unimplemented(format!("binary operator (with lvalue): {:?}", bop))),
                        }
                    } else {
                        let tl = self.compile_expression(&ec, &boe.node.lhs)?;
                        let tr = self.compile_expression(&ec, &boe.node.rhs)?;
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
                        match &boe.node.operator.node {
                            ast::BinaryOperator::Plus => self.ins.tructions().push(vm::Instruction::Add),
                            ast::BinaryOperator::Minus => self.ins.tructions().push(vm::Instruction::Sub),
                            ast::BinaryOperator::Multiply => self.ins.tructions().push(vm::Instruction::Mul),
                            ast::BinaryOperator::Less => self.ins.tructions().push(vm::Instruction::Less),
                            ast::BinaryOperator::Greater => {
                                self.ins.tructions().push(vm::Instruction::Swap);
                                self.ins.tructions().push(vm::Instruction::Less);
                            },
                            bop => return ec.erm(ErrorKind::Unimplemented(format!("binary operator: {:?}", bop))),
                        }
                        Ok(tl) // TODO: actually pick the right type instead of The Left One

                    }
                },
                _ => return ec.erm(ErrorKind::Unimplemented(format!("expression: {:?}", e))),
            }
        })
    }
}
