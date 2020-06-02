use crate::code;
use crate::lexer;
use crate::parser;
use crate::parser::ast;
use crate::vm::object;

use anyhow::Result;

#[derive(Debug, Default)]
pub struct Compiler {
    instructions: code::Instructions,
    constants: Vec<object::Object>,
}

impl Compiler {
    pub fn compile(&self, node: ast::Node) -> Result<()> {
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct Bytecode {
    instructions: code::Instructions,
    constants: Vec<object::Object>,
}

impl From<Compiler> for Bytecode {
    fn from(value: Compiler) -> Self {
        Self {
            instructions: value.instructions,
            constants: value.constants,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    enum Type {
        Int(i64),
    }

    #[test]
    fn test_compiler() {
        let tests = vec![(
            "1 + 2",
            vec![Type::Int(1), Type::Int(2)],
            vec![
                code::OpConstant(0).to_bytes().to_vec(),
                code::OpConstant(1).to_bytes().to_vec(),
            ],
        )];

        run_compiler_tests(tests);
    }

    fn run_compiler_tests(tests: Vec<(&str, Vec<Type>, Vec<code::Instructions>)>) {
        tests
            .into_iter()
            .for_each(|(input, expected_constants, expected_instructure)| {
                let program = parse_test_input(input);
                let compiler = Compiler::default();
                if let Err(e) = compiler.compile(program.into()) {
                    panic!("{}", e);
                };

                let Bytecode {
                    instructions,
                    constants,
                } = compiler.into();

                test_instructions(instructions, expected_instructure);
                test_constants(constants, expected_constants);
            });
    }

    fn test_instructions(actual: code::Instructions, expected: Vec<code::Instructions>) {
        let expected = expected.into_iter().flatten().collect::<Vec<_>>();
        assert_eq!(actual, expected);
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
