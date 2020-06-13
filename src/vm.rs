pub mod bytecode;
pub mod convert;
pub mod opcode;

use crate::compiler;
use crate::evaluator::object;
use crate::vm::bytecode::Instructions;
use crate::vm::convert::Read;

mod preludes {
    pub use super::super::preludes::*;
    pub use crate::vm;
}

use preludes::*;

const STACK_SIZE: usize = 2048;

#[derive(Debug, Default)]
pub struct VM {
    constants: Vec<object::Object>,
    instructions: Instructions,
    stacks: Vec<object::Object>,
    sp: usize,
}

impl From<bytecode::Bytecode> for VM {
    fn from(value: bytecode::Bytecode) -> Self {
        Self {
            constants: value.constants,
            instructions: value.instructions,
            stacks: Vec::with_capacity(STACK_SIZE),
            ..Self::default()
        }
    }
}

impl VM {
    pub fn stack_top(&self) -> Option<&object::Object> {
        if self.sp == 0 {
            None
        } else {
            Some(&self.stacks[self.sp - 1])
        }
    }

    pub fn last_popped_stack_elem(&self) -> &object::Object {
        &self.stacks[self.sp]
    }

    pub fn run(&mut self) -> Result<()> {
        let mut ip = 0;

        while ip < self.instructions.0.len() {
            let op = opcode::Opcode::try_from(&self.instructions.0[ip..])?;
            match &op {
                opcode::Opcode::Constant(constant) => {
                    let const_idx = constant.0;

                    // TODO: Rc<object::Object> ?
                    self.push(self.constants[usize::from(const_idx)].clone())?;
                }
                opcode::Opcode::Add(_)
                | opcode::Opcode::Sub(_)
                | opcode::Opcode::Mul(_)
                | opcode::Opcode::Div(_) => self.execute_binary_operation(&op)?,
                opcode::Opcode::Pop(_) => {
                    self.pop();
                }
            }
            ip += 1 + op.readsize();
        }

        Ok(())
    }

    fn execute_binary_operation(&mut self, op: &opcode::Opcode) -> Result<()> {
        match self.pop_pair() {
            (object::Object::Integer(i1), object::Object::Integer(i2)) => {
                self.execute_binary_integer_operation(op, i1.value, i2.value)?;
            }
            (unknown_obj1, unknown_obj2) => Err(anyhow::format_err!(
                "unsupported types for binary operation: {} {}",
                unknown_obj1,
                unknown_obj2
            ))?,
        }

        Ok(())
    }

    fn execute_binary_integer_operation(
        &mut self,
        op: &opcode::Opcode,
        left_val: i64,
        right_val: i64,
    ) -> Result<()> {
        let value = match op {
            opcode::Opcode::Add(_) => left_val + right_val,
            opcode::Opcode::Sub(_) => left_val - right_val,
            opcode::Opcode::Mul(_) => left_val * right_val,
            opcode::Opcode::Div(_) => left_val / right_val,
            _ => Err(anyhow::format_err!(
                "unknown integer operator. received {}",
                op
            ))?,
        };

        self.push(object::Integer { value }.into())?;
        Ok(())
    }

    fn pop_pair(&mut self) -> (&object::Object, &object::Object) {
        let o = (&self.stacks[self.sp - 1], &self.stacks[self.sp - 2]);
        self.sp -= 2;
        o
    }

    fn pop(&mut self) -> &object::Object {
        let o = &self.stacks[self.sp - 1];
        self.sp -= 1;
        o
    }

    fn push(&mut self, o: object::Object) -> Result<()> {
        if self.sp >= STACK_SIZE {
            Err(anyhow::format_err!("stack overflow"))?;
        }

        self.stacks.insert(self.sp, o);
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
        let tests: Tests = vec![
            ("1", 1),
            ("2", 2),
            ("1 + 2", 3),
            ("1 - 2", -1),
            ("1 * 2", 2),
            ("4 / 2", 2),
            ("50 / 2 * 2 + 10 - 5", 55),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("5 * (2 + 10)", 60),
        ]
        .into();
        run_vm_tests(tests);
    }

    fn run_vm_tests(tests: Tests) {
        tests.0.into_iter().for_each(|(input, expected)| {
            let program = parse(input.as_str());
            let mut comp = compiler::Compiler::default();
            if let Err(e) = comp.compile(program.into()) {
                panic!(format!("compiler error {}: ", e));
            }
            let bytecode: bytecode::Bytecode = comp.into();
            let debug = bytecode.clone();

            let mut vm = VM::from(bytecode);
            if let Err(e) = vm.run() {
                panic!("vm error: {} by {:?}", e, debug);
            }

            let stack_elem = vm.last_popped_stack_elem();

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
