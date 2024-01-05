use crate::vm;

use std::collections::HashMap;
use lang_c::ast as ast;

pub struct Scope {
    pub entries: HashMap<String, u64>,
}

impl Scope {
    pub fn new() -> Self {
        Self {
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
    if let ast::DeclaratorKind::Identifier(i) = d.kind.node {
        i.node.name
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

    fn sizeof(&self, t: lang_c::ast::TypeSpecifier) -> u64 {
        match t {
            Void => 0,
            Char => 1,
            Short => 2,
            Int => 4,
            Long => 8,
            Float => 4,
            Double => 8,
            Signed => 4,
            Unsigned => 4,
            Bool => 1,
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
    }

    fn compile_definition(&mut self, d: ast::FunctionDefinition) {
        let name = declarator_identifier(&d.declarator.node);
        self.functions.insert(name.clone(), self.pc());
        let mut offset = 0;
        let params: HashMap<String, u64> = if let ast::DerivedDeclarator::Function(f) = d.declarator.node.derived[0].node {
            f.node.parameters.iter().map(|n| {
                let nm = declarator_identifier(&n.node.declarator.expect("missing parameter name").node);
                let ret = (nm, offset);
                offset += if let ast::DeclarationSpecifier::TypeSpecifier(t) = n.node.specifiers[0].node {
                    self.sizeof(t.node)
                } else {
                    4
                };
                ret
            }).collect()
        } else {
            panic!("invalid function declarator");
        };
        self.block_scopes.push(Scope { entries: params });
        // generate code to handle args
        self.compile_statement(d.statement.node);
        self.block_scopes.pop();
    }

    fn compile_statement(&mut self, d: ast::Statement) {
    }
}
