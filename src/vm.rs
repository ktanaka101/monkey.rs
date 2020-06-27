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
const TRUE: object::Boolean = object::Boolean { value: true };
const FALSE: object::Boolean = object::Boolean { value: false };
const NULL: object::Null = object::Null {};

#[derive(Debug, Default)]
struct Stack {
    data: Vec<object::Object>,
    pointer: usize,
}

impl Stack {
    fn new() -> Self {
        Self {
            data: Vec::with_capacity(STACK_SIZE),
            ..Self::default()
        }
    }

    fn top(&self) -> Option<&object::Object> {
        if self.pointer == 0 {
            None
        } else {
            Some(&self.data[self.pointer - 1])
        }
    }

    fn last_popped(&self) -> &object::Object {
        &self.data[self.pointer]
    }

    fn push(&mut self, o: object::Object) -> Result<()> {
        if self.pointer >= STACK_SIZE {
            Err(anyhow::format_err!("stack overflow"))?;
        }

        if self.pointer == self.data.len() {
            self.data.push(o);
        } else if self.pointer < self.data.len() {
            self.data[self.pointer] = o;
        } else {
            unreachable!(
                "null pointer. data: {:?} pointer: {:?}",
                self.data, self.pointer
            );
        }
        self.pointer += 1;

        Ok(())
    }

    fn pop(&mut self) -> &object::Object {
        let o = &self.data[self.pointer - 1];
        self.pointer -= 1;
        o
    }

    fn pop_pair(&mut self) -> (&object::Object, &object::Object) {
        let o = (&self.data[self.pointer - 2], &self.data[self.pointer - 1]);
        self.pointer -= 2;
        o
    }
}

#[derive(Debug, Default)]
pub struct VM {
    constants: Vec<object::Object>,
    instructions: Instructions,
    stack: Stack,
}

impl From<bytecode::Bytecode> for VM {
    fn from(value: bytecode::Bytecode) -> Self {
        Self {
            constants: value.constants,
            instructions: value.instructions,
            stack: Stack::new(),
        }
    }
}

impl VM {
    pub fn stack_top(&self) -> Option<&object::Object> {
        self.stack.top()
    }

    pub fn last_popped_stack_elem(&self) -> &object::Object {
        self.stack.last_popped()
    }

    pub fn run(&mut self) -> Result<()> {
        let mut ip = 0;

        while ip < self.instructions.0.len() {
            let op = opcode::Opcode::try_from(&self.instructions.0[ip..])?;
            match &op {
                opcode::Opcode::Constant(constant) => {
                    let const_idx = constant.0;

                    // TODO: Rc<object::Object> ?
                    self.stack
                        .push(self.constants[usize::from(const_idx)].clone())?;
                }
                opcode::Opcode::Add(_)
                | opcode::Opcode::Sub(_)
                | opcode::Opcode::Mul(_)
                | opcode::Opcode::Div(_) => self.execute_binary_operation(&op)?,
                opcode::Opcode::Pop(_) => {
                    self.stack.pop();
                }
                opcode::Opcode::True(_) => {
                    self.stack.push(TRUE.into())?;
                }
                opcode::Opcode::False(_) => {
                    self.stack.push(FALSE.into())?;
                }
                opcode::Opcode::Equal(_)
                | opcode::Opcode::NotEqual(_)
                | opcode::Opcode::GreaterThan(_) => self.execute_comparison(&op)?,
                opcode::Opcode::Bang(_) => {
                    self.execute_bang_oeprator()?;
                }
                opcode::Opcode::Minus(_) => {
                    self.execute_minus_operator()?;
                }
                opcode::Opcode::JumpNotTruthy(jump) => {
                    ip += 2;

                    let cond = self.stack.pop();
                    if !Self::is_truthy(cond) {
                        ip = usize::from(jump.0) - 1;
                    }

                    ip -= jump.readsize();
                }
                opcode::Opcode::Jump(jump) => {
                    ip = usize::from(jump.0) - 1;

                    ip -= jump.readsize();
                }
                opcode::Opcode::Null(_) => {
                    self.stack.push(NULL.into())?;
                }
            }
            ip += 1 + op.readsize();
        }

        Ok(())
    }

    fn execute_binary_operation(&mut self, op: &opcode::Opcode) -> Result<()> {
        match self.stack.pop_pair() {
            (object::Object::Integer(i1), object::Object::Integer(i2)) => {
                let int = Self::execute_binary_integer_operation(op, i1.value, i2.value)?;
                self.stack.push(int.into())?;
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
        op: &opcode::Opcode,
        left_val: i64,
        right_val: i64,
    ) -> Result<object::Integer> {
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

        Ok(object::Integer { value })
    }

    fn execute_comparison(&mut self, op: &opcode::Opcode) -> Result<()> {
        let (right, left) = self.stack.pop_pair();

        match (left, right) {
            (object::Object::Integer(l), object::Object::Integer(r)) => {
                let compared =
                    Self::execute_integer_comparison(op, &l.clone().into(), &r.clone().into())?;
                self.stack.push(compared.into())?;
            }
            (l, r) => match op {
                opcode::Opcode::Equal(_) => {
                    let b = Self::native_bool_to_boolean_object(l == r);
                    self.stack.push(b.into())?;
                }
                opcode::Opcode::NotEqual(_) => {
                    let b = Self::native_bool_to_boolean_object(l != r);
                    self.stack.push(b.into())?;
                }
                unknown_op => Err(anyhow::format_err!(
                    "unknown operator: {} ({} {})",
                    unknown_op,
                    l,
                    r
                ))?,
            },
        };

        Ok(())
    }

    fn execute_integer_comparison(
        op: &opcode::Opcode,
        left: &object::Object,
        right: &object::Object,
    ) -> Result<object::Boolean> {
        match (left, right) {
            (object::Object::Integer(l), object::Object::Integer(r)) => match op {
                opcode::Opcode::Equal(_) => {
                    Ok(Self::native_bool_to_boolean_object(r.value == l.value))
                }
                opcode::Opcode::NotEqual(_) => {
                    Ok(Self::native_bool_to_boolean_object(r.value != l.value))
                }
                opcode::Opcode::GreaterThan(_) => {
                    Ok(Self::native_bool_to_boolean_object(r.value > l.value))
                }
                unknown_op => Err(anyhow::format_err!(
                    "unknown operator: {} ({}  {})",
                    unknown_op,
                    l,
                    r
                ))?,
            },
            (unknown_l, unknown_r) => Err(anyhow::format_err!(
                "expected (Integer, Integer). received ({}  {})",
                unknown_l,
                unknown_r
            ))?,
        }
    }

    fn native_bool_to_boolean_object(b: bool) -> object::Boolean {
        if b {
            TRUE
        } else {
            FALSE
        }
    }

    fn execute_bang_oeprator(&mut self) -> Result<()> {
        let operand = self.stack.pop();
        match operand {
            object::Object::Boolean(b) => {
                if b.value {
                    self.stack.push(FALSE.into())?;
                } else {
                    self.stack.push(TRUE.into())?;
                }
            }
            object::Object::Null(_) => {
                self.stack.push(TRUE.into())?;
            }
            _other => self.stack.push(FALSE.into())?,
        };

        Ok(())
    }

    fn execute_minus_operator(&mut self) -> Result<()> {
        let operand = self.stack.pop();
        match operand {
            object::Object::Integer(i) => {
                let int = object::Integer { value: -i.value };
                self.stack.push(int.into())?
            }
            unknown => Err(anyhow::format_err!(
                "unsupported type fot negation: {}",
                unknown
            ))?,
        };

        Ok(())
    }

    fn is_truthy(obj: &object::Object) -> bool {
        match obj {
            object::Object::Boolean(b) => b.value,
            object::Object::Null(_) => false,
            _other => true,
        }
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
        Bool(bool),
        Null,
    }

    struct Tests(Vec<(String, Expected)>);

    impl From<i64> for Expected {
        fn from(value: i64) -> Self {
            Self::Int(value)
        }
    }

    impl From<bool> for Expected {
        fn from(value: bool) -> Self {
            Self::Bool(value)
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
            ("-5", -5),
            ("-10", -10),
            ("-50 + 100 + -50", 0),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_boolean_expressions() {
        let tests: Tests = vec![
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false == true", false),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
            ("!true", false),
            ("!false", true),
            ("!5", false),
            ("!!true", true),
            ("!!false", false),
            ("!!5", true),
            ("!(if (false) { 5; })", true),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_conditional() {
        let tests: Tests = vec![
            ("if (true) { 10 }", 10),
            ("if (true) { 10 } else { 20 }", 10),
            ("if (false) { 10 } else { 20 }", 20),
            ("if (1) { 10 }", 10),
            ("if (1 < 2) { 10 }", 10),
            ("if (1 < 2) { 10 } else { 20 }", 10),
            ("if (1 > 2) { 10 } else { 20 }", 20),
            ("if ((if (false) { 10 })) { 10 } else { 20 }", 20),
        ]
        .into();
        run_vm_tests(tests);

        let tests: Tests = vec![
            ("if (1 > 2) { 10 }", Expected::Null),
            ("if (false) { 10 }", Expected::Null),
        ]
        .into();
        run_vm_tests(tests);
    }

    fn run_vm_tests(tests: Tests) {
        tests.0.into_iter().for_each(|(input, expected)| {
            let program = parse(input.as_str());
            let mut sym_table = Default::default();
            let mut constants = Default::default();
            let mut comp = compiler::Compiler::new_with_state(&mut sym_table, &mut constants);
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
            Expected::Bool(expected_bool) => {
                test_bool_object(actual, *expected_bool);
            }
            Expected::Null => {
                test_null_object(actual);
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

    fn test_bool_object(actual: &object::Object, expected: bool) {
        let result = match actual {
            object::Object::Boolean(b) => b,
            obj => panic!("expected Boolean. received {}", obj),
        };
        assert_eq!(result.value, expected);
    }

    fn test_null_object(actual: &object::Object) {
        match actual {
            object::Object::Null(_) => (),
            obj => panic!("expected Null. received {}", obj),
        };
    }

    fn parse(input: &str) -> ast::Program {
        let l = lexer::Lexer::new(input.into());
        let mut p = parser::Parser::new(l);
        p.parse_program().unwrap()
    }
}
