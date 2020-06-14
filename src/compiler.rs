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
                ast::Stmt::ExprStmt(stmt) => {
                    self.compile(stmt.expr.into())?;
                    self.emit(opcode::Pop.into());
                }
                _ => unimplemented!(),
            },
            ast::Node::Expr(expr) => match expr {
                ast::Expr::InfixExpr(expr) => {
                    if expr.ope == ast::Operator::Lt {
                        self.compile((*expr.right).into())?;
                        self.compile((*expr.left).into())?;
                        self.emit(opcode::GreaterThan.into());
                    } else {
                        self.compile((*expr.left).into())?;
                        self.compile((*expr.right).into())?;

                        match expr.ope {
                            ast::Operator::Plus => self.emit(opcode::Add.into()),
                            ast::Operator::Minus => self.emit(opcode::Sub.into()),
                            ast::Operator::Asterisk => self.emit(opcode::Mul.into()),
                            ast::Operator::Slash => self.emit(opcode::Div.into()),
                            ast::Operator::Gt => self.emit(opcode::GreaterThan.into()),
                            ast::Operator::Equal => self.emit(opcode::Equal.into()),
                            ast::Operator::NotEqual => self.emit(opcode::NotEqual.into()),
                            ast::Operator::Lt => unreachable!(),
                            unknown => Err(anyhow::format_err!("unknown operator {}", unknown))?,
                        };
                    }
                }
                ast::Expr::Integer(int) => {
                    let int = object::Integer { value: int.value };
                    let op = opcode::Constant::from(self.add_constant(int.into()));
                    self.emit(op.into());
                }
                ast::Expr::Boolean(b) => {
                    self.emit(match b.value {
                        true => opcode::True.into(),
                        false => opcode::False.into(),
                    });
                }
                _ => unimplemented!(),
            },
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
        let expected: Vec<opcode::Opcode> = vec![
            opcode::Constant(0).into(),
            opcode::Constant(1).into(),
            opcode::Add.into(),
            opcode::Pop.into(),
        ];
        let tests = vec![("1 + 2", vec![Type::Int(1), Type::Int(2)], expected.into())];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_integer_arithmetic() {
        let tests: Vec<(&str, Vec<Type>, bytecode::Instructions)> = vec![
            (
                "1 + 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Add),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1 - 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Sub),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1 * 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Mul),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1 / 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Div),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1; 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Pop),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_boolean_expressions() {
        let tests: Vec<(&str, Vec<Type>, bytecode::Instructions)> = vec![
            (
                "true",
                vec![],
                vec![
                    opcode::Opcode::from(opcode::True),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "false",
                vec![],
                vec![
                    opcode::Opcode::from(opcode::False),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1 > 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::GreaterThan),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1 < 2",
                vec![Type::Int(2), Type::Int(1)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::GreaterThan),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1 == 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Equal),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "1 != 2",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::NotEqual),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "true == false",
                vec![],
                vec![
                    opcode::Opcode::from(opcode::True),
                    opcode::Opcode::from(opcode::False),
                    opcode::Opcode::from(opcode::Equal),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "true != false",
                vec![],
                vec![
                    opcode::Opcode::from(opcode::True),
                    opcode::Opcode::from(opcode::False),
                    opcode::Opcode::from(opcode::NotEqual),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
        ];

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
        assert_eq!(actual.to_string(), expected.to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_format_instructions() {
        let tests: Vec<(Vec<opcode::Opcode>, &str)> = vec![
            (
                vec![opcode::Constant(65534).into(), opcode::Constant(1).into()],
                "0000 Constant 65534¥n0003 Constant 1¥n",
            ),
            (
                vec![opcode::Constant(65534).into()],
                "0000 Constant 65534¥n",
            ),
            (
                vec![
                    opcode::Constant(1).into(),
                    opcode::Constant(2).into(),
                    opcode::Add.into(),
                ],
                "0000 Constant 1¥n0003 Constant 2¥n0006 Add¥n",
            ),
            (vec![opcode::Sub.into()], "0000 Sub¥n"),
            (vec![opcode::Mul.into()], "0000 Mul¥n"),
            (vec![opcode::Div.into()], "0000 Div¥n"),
            (vec![opcode::Pop.into()], "0000 Pop¥n"),
            (vec![opcode::True.into()], "0000 True¥n"),
            (vec![opcode::False.into()], "0000 False¥n"),
            (vec![opcode::Equal.into()], "0000 Equal¥n"),
            (vec![opcode::NotEqual.into()], "0000 NotEqual¥n"),
            (vec![opcode::GreaterThan.into()], "0000 GreaterThan¥n"),
        ];

        tests.into_iter().for_each(|(input, expected)| {
            let instructions: bytecode::Instructions = input
                .into_iter()
                .flat_map(|v| v.to_bytes().to_vec())
                .collect::<Vec<bytecode::Instruction>>()
                .into();
            assert_eq!(format!("{}", instructions), expected);
        });
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
