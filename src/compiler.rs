pub mod convert;
mod symbol_table;

use crate::evaluator::object;
use crate::parser::ast;
use crate::vm::{bytecode, opcode};
use convert::ToBytes;

pub use symbol_table::SymbolTable;

mod preludes {
    pub use super::super::preludes::*;
}

use preludes::*;

#[derive(Debug)]
pub struct Compiler<'a> {
    instructions: bytecode::Instructions,
    constants: &'a mut Vec<object::Object>,
    last_instruction: Option<EmittedInstruction>,
    prev_instruction: Option<EmittedInstruction>,
    symbol_table: &'a mut symbol_table::SymbolTable,
}

#[derive(Debug, Clone)]
struct EmittedInstruction {
    opcode: opcode::Opcode,
    position: Pos,
}

type Pos = u16;

impl<'a> Compiler<'a> {
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
                ast::Stmt::Block(block) => {
                    block
                        .statements
                        .into_iter()
                        .try_for_each(|stmt| self.compile(stmt.into()))?;
                }
                ast::Stmt::Let(l) => {
                    self.compile(l.value.into())?;
                    let symbol = self.symbol_table.define(l.name.value);
                    match symbol {
                        symbol_table::Symbol::Global { index, .. } => {
                            let op = opcode::SetGlobal(*index).into();
                            self.emit(op);
                        }
                    };
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
                ast::Expr::PrefixExpr(expr) => {
                    self.compile((*expr.right).into())?;

                    match expr.ope {
                        ast::Operator::Minus => self.emit(opcode::Minus.into()),
                        ast::Operator::Bang => self.emit(opcode::Bang.into()),
                        unknown => Err(anyhow::format_err!("unknown operator {}", unknown))?,
                    };
                }
                ast::Expr::If(expr) => {
                    self.compile((*expr.cond).into())?;

                    let jump_not_truthy_pos = self.emit(opcode::JumpNotTruthy(9999).into());

                    self.compile(ast::Stmt::from(expr.consequence).into())?;

                    if self.last_instruction_is_pop() {
                        self.remove_last_pop()?;
                    }

                    let jump_pos = self.emit(opcode::Jump(9999).into());
                    self.change_operand(jump_not_truthy_pos, self.instructions.0.len())?;

                    if let Some(alternative) = expr.alternative {
                        self.compile(ast::Stmt::from(alternative).into())?;
                        if self.last_instruction_is_pop() {
                            self.remove_last_pop()?;
                        }
                    } else {
                        self.emit(opcode::Null.into());
                    }

                    self.change_operand(jump_pos, self.instructions.0.len())?;
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
                ast::Expr::StringLit(s) => {
                    let s = object::StringLit { value: s.value };
                    let op = opcode::Constant::from(self.add_constant(s.into()));
                    self.emit(op.into());
                }
                ast::Expr::Identifier(id) => {
                    let symbol = self.symbol_table.resolve(&id.value);
                    match symbol {
                        Some(symbol) => match symbol {
                            symbol_table::Symbol::Global { index, .. } => {
                                let op = opcode::GetGlobal(*index).into();
                                self.emit(op);
                            }
                        },
                        None => Err(anyhow::format_err!("undefined variable {}", id.value))?,
                    };
                }
                ast::Expr::Array(array) => {
                    let arr_len = array.elements.len();
                    array
                        .elements
                        .into_iter()
                        .try_for_each(|ele| self.compile(ele.into()))?;
                    self.emit(opcode::Array(arr_len.try_into()?).into());
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
        let pos = self.add_instruction(ins);

        self.set_last_instruction(op, pos);

        pos
    }

    fn set_last_instruction(&mut self, op: opcode::Opcode, pos: Pos) {
        self.prev_instruction = self.last_instruction.clone();

        let last = EmittedInstruction {
            opcode: op,
            position: pos,
        };
        self.last_instruction = Some(last);
    }

    fn last_instruction_is_pop(&self) -> bool {
        if let Some(last_inst) = &self.last_instruction {
            if let opcode::Opcode::Pop(_) = last_inst.opcode {
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    fn remove_last_pop(&mut self) -> Result<()> {
        if let Some(last_isnt) = &self.last_instruction {
            let instructions =
                bytecode::Instructions(self.instructions.0[..last_isnt.position.into()].into());
            self.instructions = instructions;
            self.last_instruction = self.prev_instruction.clone();

            Ok(())
        } else {
            Err(anyhow::format_err!("uninitialized"))?
        }
    }

    fn replace_instructions(&mut self, pos: Pos, new_instructions: bytecode::Instructions) {
        new_instructions
            .0
            .into_iter()
            .enumerate()
            .for_each(|(i, inst)| {
                self.instructions.0[i + usize::from(pos)] = inst;
            });
    }

    fn change_operand(&mut self, op_pos: Pos, operand: usize) -> Result<()> {
        let op = opcode::Opcode::try_from(&self.instructions.0[usize::from(op_pos)..])?;
        match op {
            opcode::Opcode::JumpNotTruthy(mut op) => {
                op.0 = u16::try_from(operand)?;
                self.replace_instructions(op_pos, op.into());
            }
            opcode::Opcode::Jump(mut op) => {
                op.0 = u16::try_from(operand)?;
                self.replace_instructions(op_pos, op.into());
            }
            _ => Err(anyhow::format_err!("Expected "))?,
        }

        Ok(())
    }
}

impl<'a> Compiler<'a> {
    pub fn new_with_state(
        sym_table: &'a mut symbol_table::SymbolTable,
        constants: &'a mut Vec<object::Object>,
    ) -> Self {
        Self {
            symbol_table: sym_table,
            constants: constants,
            instructions: Default::default(),
            last_instruction: Default::default(),
            prev_instruction: Default::default(),
        }
    }
}

impl<'a> From<Compiler<'a>> for crate::vm::bytecode::Bytecode {
    fn from(value: Compiler<'a>) -> Self {
        Self {
            instructions: value.instructions,
            constants: value.constants.clone(),
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
        String(String),
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
            (
                "-1",
                vec![Type::Int(1)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Minus),
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
            (
                "!true",
                vec![],
                vec![
                    opcode::Opcode::from(opcode::True),
                    opcode::Opcode::from(opcode::Bang),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "!false",
                vec![],
                vec![
                    opcode::Opcode::from(opcode::False),
                    opcode::Opcode::from(opcode::Bang),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_conditionals() {
        let tests: Vec<(&str, Vec<Type>, bytecode::Instructions)> = vec![
            (
                "if (true) { 10 }; 3333;",
                vec![Type::Int(10), Type::Int(3333)],
                vec![
                    opcode::Opcode::from(opcode::True),
                    opcode::Opcode::from(opcode::JumpNotTruthy(10)),
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Jump(11)),
                    opcode::Opcode::from(opcode::Null),
                    opcode::Opcode::from(opcode::Pop),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "if (true) { 10 } else { 20 }; 3333;",
                vec![Type::Int(10), Type::Int(20), Type::Int(3333)],
                vec![
                    opcode::Opcode::from(opcode::True),
                    opcode::Opcode::from(opcode::JumpNotTruthy(10)),
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Jump(13)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Pop),
                    opcode::Opcode::from(opcode::Constant(2)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_global_let_statements() {
        let tests: Vec<(&str, Vec<Type>, bytecode::Instructions)> = vec![
            (
                "
                let one = 1;
                let two = 2;
                ",
                vec![Type::Int(1), Type::Int(2)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::SetGlobal(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::SetGlobal(1)),
                ]
                .into(),
            ),
            (
                "
                let one = 1;
                one;
                ",
                vec![Type::Int(1)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::SetGlobal(0)),
                    opcode::Opcode::from(opcode::GetGlobal(0)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "
                let one = 1;
                let two = one;
                two;
                ",
                vec![Type::Int(1)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::SetGlobal(0)),
                    opcode::Opcode::from(opcode::GetGlobal(0)),
                    opcode::Opcode::from(opcode::SetGlobal(1)),
                    opcode::Opcode::from(opcode::GetGlobal(1)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_string_expressions() {
        let tests: Vec<(&str, Vec<Type>, bytecode::Instructions)> = vec![
            (
                r#""monkey""#,
                vec![Type::String("monkey".into())],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                r#""mon" + "key""#,
                vec![Type::String("mon".into()), Type::String("key".into())],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Add),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
        ];

        run_compiler_tests(tests);
    }

    #[test]
    fn test_array_literals() {
        let tests: Vec<(&str, Vec<Type>, bytecode::Instructions)> = vec![
            (
                "[]",
                vec![],
                vec![
                    opcode::Opcode::from(opcode::Array(0)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "[1, 2, 3]",
                vec![Type::Int(1), Type::Int(2), Type::Int(3)],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Constant(2)),
                    opcode::Opcode::from(opcode::Array(3)),
                    opcode::Opcode::from(opcode::Pop),
                ]
                .into(),
            ),
            (
                "[1 + 2, 3 - 4, 5 * 6]",
                vec![
                    Type::Int(1),
                    Type::Int(2),
                    Type::Int(3),
                    Type::Int(4),
                    Type::Int(5),
                    Type::Int(6),
                ],
                vec![
                    opcode::Opcode::from(opcode::Constant(0)),
                    opcode::Opcode::from(opcode::Constant(1)),
                    opcode::Opcode::from(opcode::Add),
                    opcode::Opcode::from(opcode::Constant(2)),
                    opcode::Opcode::from(opcode::Constant(3)),
                    opcode::Opcode::from(opcode::Sub),
                    opcode::Opcode::from(opcode::Constant(4)),
                    opcode::Opcode::from(opcode::Constant(5)),
                    opcode::Opcode::from(opcode::Mul),
                    opcode::Opcode::from(opcode::Array(3)),
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
                let mut sym_table = SymbolTable::new();
                let mut constants = Vec::<object::Object>::new();
                let mut compiler = Compiler::new_with_state(&mut sym_table, &mut constants);
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
            (vec![opcode::Minus.into()], "0000 Minus¥n"),
            (vec![opcode::Bang.into()], "0000 Bang¥n"),
            (
                vec![opcode::JumpNotTruthy(65534).into()],
                "0000 JumpNotTruthy 65534¥n",
            ),
            (vec![opcode::Jump(65534).into()], "0000 Jump 65534¥n"),
            (vec![opcode::Null.into()], "0000 Null¥n"),
            (
                vec![opcode::GetGlobal(65534).into()],
                "0000 GetGlobal 65534¥n",
            ),
            (
                vec![opcode::SetGlobal(65534).into()],
                "0000 SetGlobal 65534¥n",
            ),
            (vec![opcode::Array(65534).into()], "0000 Array 65534¥n"),
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
                Type::String(s) => test_string_object(input, s.as_str()),
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

    fn test_string_object(actual: object::Object, expected: &str) {
        match actual {
            object::Object::StringLit(s) => {
                assert_eq!(s.value, expected);
            }
            o => panic!("expected object::StringLit. received {}", o),
        }
    }

    fn parse_test_input(input: &str) -> ast::Program {
        let l = lexer::Lexer::new(input.into());
        let mut p = parser::Parser::new(l);
        p.parse_program().unwrap()
    }
}
