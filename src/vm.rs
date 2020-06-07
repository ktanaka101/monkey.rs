use std::convert::TryFrom;

use anyhow::Result;

use crate::code;
use crate::code::Read;
use crate::compiler;
use crate::evaluator::object;

const STACK_SIZE: usize = 2048;

#[derive(Debug, Default)]
struct VM {
    constants: Vec<object::Object>,
    instructions: code::Instructions,
    stacks: Vec<object::Object>,
    sp: usize,
}

impl From<compiler::Bytecode> for VM {
    fn from(value: compiler::Bytecode) -> Self {
        Self {
            constants: value.constants,
            instructions: value.instructions,
            stacks: Vec::with_capacity(STACK_SIZE),
            ..Self::default()
        }
    }
}

impl VM {
    fn stack_top(&self) -> Option<&object::Object> {
        if self.sp == 0 {
            None
        } else {
            Some(&self.stacks[self.sp - 1])
        }
    }

    fn run(&mut self) -> Result<()> {
        let mut ip = 0;

        while ip < self.instructions.0.len() {
            let op = code::Opcode::try_from(&self.instructions.0[ip..])?;
            match op {
                code::Opcode::OpConstant(constant) => {
                    let const_idx = constant.0;
                    ip = ip + usize::from(code::OpConstant::readsize());

                    // TODO: Rc<object::Object> ?
                    self.push(self.constants[usize::from(const_idx)].clone())?;
                }
            }

            ip += 1;
        }

        Ok(())
    }

    fn push(&mut self, o: object::Object) -> Result<()> {
        if self.sp >= STACK_SIZE {
            Err(anyhow::format_err!("stack overflow"))?;
        }

        self.stacks.push(o);
        self.sp += 1;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer;
    use crate::parser;
    use crate::parser::ast;

    use super::*;

    enum Expected {
        Int(i64),
    }

    struct Tests(Vec<(String, Expected)>);

    impl From<i64> for Expected {
        fn from(value: i64) -> Self {
            Self::Int(value)
        }
    }

    impl<T> From<Vec<(&str, T)>> for Tests
    where
        T: Into<Expected>,
    {
        fn from(value: Vec<(&str, T)>) -> Self {
            let tests = value
                .into_iter()
                .map(|(input, expected)| (input.to_string(), expected.into()))
                .collect::<Vec<_>>();

            Tests(tests)
        }
    }

    #[test]
    fn test_integer_arithmetic() {
        let tests: Tests = vec![("1", 1), ("2", 2), ("1 + 2", 2)].into();
        run_vm_tests(tests);
    }

    fn run_vm_tests(tests: Tests) {
        tests.0.into_iter().for_each(|(input, expected)| {
            let program = parse(input.as_str());
            let mut comp = compiler::Compiler::default();
            if let Err(e) = comp.compile(program.into()) {
                panic!(format!("compiler error {}: ", e));
            }
            let bytecode: compiler::Bytecode = comp.into();
            let debug = bytecode.clone();

            let mut vm = VM::from(bytecode);
            if let Err(e) = vm.run() {
                panic!("vm error: {} by {:?}", e, debug);
            }

            let stack_elem = vm.stack_top().unwrap();

            test_object(stack_elem, &expected);
        });
    }

    fn test_object(actual: &object::Object, expected: &Expected) {
        match expected {
            Expected::Int(expected_int) => {
                test_integer_object(actual, *expected_int);
            }
        }
    }

    fn test_integer_object(actual: &object::Object, expected: i64) {
        let result = match actual {
            object::Object::Integer(int) => int,
            obj => panic!("expected Integer. received {}", obj),
        };

        assert_eq!(result.value, expected);
    }
    fn parse(input: &str) -> ast::Program {
        let l = lexer::Lexer::new(input.into());
        let mut p = parser::Parser::new(l);
        p.parse_program().unwrap()
    }
}
