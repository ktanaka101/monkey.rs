pub mod convert;

use crate::evaluator::object;
use crate::parser::ast;
use crate::vm::{bytecode, opcode};

mod preludes {
    pub use super::super::preludes::*;
}

use preludes::*;

#[derive(Debug, Default)]
pub struct Compiler {
    instructions: bytecode::Instructions,
    constants: Vec<object::Object>,
}

type Pos = u16;

impl Compiler {
    pub fn compile(&mut self, node: ast::Node) -> Result<()> {
        match node {
            ast::Node::Program(pg) => {
                pg.statements
                    .into_iter()
                    .try_for_each(|stmt| self.compile(stmt.into()))?;
            }
            ast::Node::Stmt(stmt) => match stmt {
                ast::Stmt::ExprStmt(stmt) => self.compile(stmt.expr.into())?,
                _ => unimplemented!(),
            },
            ast::Node::Expr(expr) => match expr {
                ast::Expr::InfixExpr(expr) => {
                    self.compile((*expr.left).into())?;
                    self.compile((*expr.right).into())?;
                }
                ast::Expr::Integer(int) => {
                    let int = object::Integer { value: int.value };
                    let op = opcode::OpConstant::from(self.add_constant(int.into()));
                    self.emit(op.into());
                }
                _ => unimplemented!(),
            },
            _ => unimplemented!(),
        }
        Ok(())
    }

    fn add_constant(&mut self, obj: object::Object) -> Pos {
        self.constants.push(obj);
        Pos::try_from(self.constants.len()).unwrap() - 1
    }

    fn add_instruction(&mut self, mut ins: Vec<bytecode::Instruction>) -> Pos {
        let len = Pos::try_from(self.instructions.0.len()).unwrap();
        self.instructions.0.append(&mut ins);
        len
    }

    fn emit(&mut self, op: opcode::Opcode) -> Pos {
        let ins = op.to_bytes();
        self.add_instruction(ins)
    }
}

impl From<Compiler> for crate::vm::bytecode::Bytecode {
    fn from(value: Compiler) -> Self {
        Self {
            instructions: value.instructions,
            constants: value.constants,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer;
    use crate::parser;

    use super::*;

    enum Type {
        Int(i64),
    }

    #[test]
    fn test_compiler() {
        let expected: Vec<opcode::Opcode> =
            vec![opcode::OpConstant(0).into(), opcode::OpConstant(1).into()];
        let tests = vec![("1 + 2", vec![Type::Int(1), Type::Int(2)], expected.into())];

        run_compiler_tests(tests);
    }

    fn run_compiler_tests(tests: Vec<(&str, Vec<Type>, bytecode::Instructions)>) {
        tests
            .into_iter()
            .for_each(|(input, expected_constants, expected_instructure)| {
                let program = parse_test_input(input);
                let mut compiler = Compiler::default();
                if let Err(e) = compiler.compile(program.into()) {
                    panic!("{}", e);
                };

                let bytecode::Bytecode {
                    instructions,
                    constants,
                } = compiler.into();

                test_instructions(instructions, expected_instructure);
                test_constants(constants, expected_constants);
            });
    }

    fn test_instructions(actual: bytecode::Instructions, expected: bytecode::Instructions) {
        assert_eq!(actual, expected.into());
    }

    #[test]
    fn test_instructions_string() {
        let instructions: Vec<bytecode::Instructions> = vec![
            opcode::OpConstant(1).into(),
            opcode::OpConstant(2).into(),
            opcode::OpConstant(65535).into(),
        ]
        .into();
        let instructions = bytecode::Instructions::from(instructions);

        let expected = "\
            0000 OpConstant 1¥n\
            0003 OpConstant 2¥n\
            0006 OpConstant 65535¥n";

        assert_eq!(instructions.to_string(), expected);
    }

    fn test_constants(actual: Vec<object::Object>, expected: Vec<Type>) {
        actual
            .into_iter()
            .zip(expected)
            .for_each(|(input, expected)| match expected {
                Type::Int(i) => {
                    test_integer_object(input, i);
                }
            });
    }

    fn test_integer_object(actual: object::Object, expected: i64) {
        match actual {
            object::Object::Integer(int_o) => {
                assert_eq!(int_o.value, expected);
            }
            o => panic!("expected object::Integer. received {}", o),
        }
    }

    fn parse_test_input(input: &str) -> ast::Program {
        let l = lexer::Lexer::new(input.into());
        let mut p = parser::Parser::new(l);
        p.parse_program().unwrap()
    }
}
