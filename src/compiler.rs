use crate::vm;

use std::collections::HashMap;
use lang_c::ast as ast;

pub struct Scope {
    pub offset: u64,
    pub entries: HashMap<String, u64>, // todo save size also :3
}

impl Scope {
    pub fn new() -> Self {
        Self {
            offset: 0,
            entries: HashMap::new(),
        }
    }
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

impl State {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            instructions: Vec::new(),
            globals: Scope::new(),
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

    fn sizeof(&self, t: &lang_c::ast::TypeSpecifier) -> u64 {
        match t {
            ast::TypeSpecifier::Void => 0,
            ast::TypeSpecifier::Char => 1,
            ast::TypeSpecifier::Short => 2,
            ast::TypeSpecifier::Int => 4,
            ast::TypeSpecifier::Long => 8,
            ast::TypeSpecifier::Float => 4,
            ast::TypeSpecifier::Double => 8,
            ast::TypeSpecifier::Signed => 4,
            ast::TypeSpecifier::Unsigned => 4,
            ast::TypeSpecifier::Bool => 1,
            _ => panic!("unsupported type in sizeof"),
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
        let ty = if let ast::DeclarationSpecifier::TypeSpecifier(t) = &d.specifiers[0].node {
            &t.node
        } else {
            panic!("non-type specifier found")
        };
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
            scope.entries.insert(nm, off);
        }
    }

    fn compile_definition(&mut self, d: ast::FunctionDefinition) {
        let name = declarator_identifier(&d.declarator.node);
        self.functions.insert(name.clone(), self.pc());
        let mut offset = 0;
        let params: HashMap<String, u64> = if let ast::DerivedDeclarator::Function(f) = &d.declarator.node.derived[0].node {
            f.node.parameters.iter().map(|n| {
                let nm = declarator_identifier(&n.node.declarator.as_ref().expect("missing parameter name").node);
                let ret = (nm, offset);
                offset += if let ast::DeclarationSpecifier::TypeSpecifier(t) = &n.node.specifiers[0].node {
                    self.sizeof(&t.node)
                } else {
                    panic!("non-type specifier found")
                };
                ret
            }).collect()
        } else {
            HashMap::new()
        };
        self.block_scopes.push(Scope { offset, entries: params });
        // generate code to handle args
        self.compile_statement(d.statement.node);
        self.block_scopes.pop();
    }

    fn compile_statement(&mut self, d: ast::Statement) {
        match d {
            ast::Statement::Expression(mn) => {
                if let Some(n) = mn {
                    self.compile_expression(n.node)
                }
            },
            ast::Statement::Compound(nodes) => {
                self.block_scopes.push(Scope::new());
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

    fn compile_expression(&mut self, e: ast::Expression) {
        match e {
            ast::Expression::Constant(c) => match c.node {
                ast::Constant::Integer(i) => {
                    let val = i.number.parse().expect("failed to parse literal");
                    self.instructions.push(vm::Instruction::Lit64(val));
                },
                co => panic!("unsupported literal: {:?}", co),
            },
            ast::Expression::BinaryOperator(boe) => {
                self.compile_expression(boe.node.lhs.node);
                self.compile_expression(boe.node.rhs.node);
                match boe.node.operator.node {
                    ast::BinaryOperator::Plus => self.instructions.push(vm::Instruction::Add),
                    bop => panic!("unsupported binary operator: {:?}", bop),
                }
            },
            _ => panic!("unsupported expression: {:?}", e),
        }
    }
}
