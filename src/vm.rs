pub mod bytecode;
pub mod convert;
mod frame;
pub mod opcode;

use crate::evaluator::builtin;
use crate::evaluator::objects;
use crate::vm::convert::Read;

mod preludes {
    pub use super::super::preludes::*;
    pub use crate::vm;
}

use preludes::*;

pub const STACK_SIZE: usize = 2048;
pub const GLOBALS_SIZE: usize = 65536;

const TRUE: objects::Boolean = objects::Boolean { value: true };
const FALSE: objects::Boolean = objects::Boolean { value: false };
const NULL: objects::Null = objects::Null {};

#[derive(Debug, Default)]
struct Stack {
    data: Vec<objects::Object>,
    pointer: usize,
}

impl Stack {
    fn new() -> Self {
        Self {
            data: vec![NULL.into(); STACK_SIZE],
            ..Self::default()
        }
    }

    fn top(&self) -> Option<&objects::Object> {
        if self.pointer == 0 {
            None
        } else {
            Some(&self.data[self.pointer - 1])
        }
    }

    fn last_popped(&self) -> &objects::Object {
        &self.data[self.pointer]
    }

    fn push(&mut self, o: objects::Object) -> Result<()> {
        if self.pointer >= STACK_SIZE {
            return Err(anyhow::format_err!("stack overflow"));
        }

        self.data[self.pointer] = o;
        self.pointer += 1;

        Ok(())
    }

    fn pop(&mut self) -> &objects::Object {
        let o = &self.data[self.pointer - 1];
        self.pointer -= 1;
        o
    }

    fn pop_pair(&mut self) -> (&objects::Object, &objects::Object) {
        let o = (&self.data[self.pointer - 2], &self.data[self.pointer - 1]);
        self.pointer -= 2;
        o
    }

    fn extract_array(&mut self, num_elements: usize) -> objects::Array {
        let elements = self.data[(self.pointer - num_elements)..self.pointer].into();
        self.pointer -= num_elements;
        objects::Array { elements }
    }

    fn extract_hash(&mut self, num_elements: usize) -> Result<objects::Hash> {
        let elements: Vec<objects::Object> =
            self.data[(self.pointer - num_elements)..self.pointer].into();

        debug_assert_eq!(elements.len() % 2, 0);

        let mut pairs = objects::HashPairs::new();
        for i in 0..(elements.len() / 2) {
            pairs.insert(
                elements[i * 2].clone().try_into()?,
                elements[i * 2 + 1].clone(),
            );
        }

        self.pointer -= num_elements;
        Ok(objects::Hash { pairs })
    }
}

#[derive(Debug)]
pub struct GlobalSpace(Vec<Option<objects::Object>>);

impl Default for GlobalSpace {
    fn default() -> Self {
        Self(vec![None; GLOBALS_SIZE])
    }
}

impl GlobalSpace {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug)]
pub struct VM<'a> {
    constants: Vec<objects::Object>,
    globals: &'a mut GlobalSpace,
    stack: Stack,
    stack_frame: frame::StackFrame,
}

impl<'a> VM<'a> {
    pub fn new_with_globals_store(
        bytecode: bytecode::Bytecode,
        globals: &'a mut GlobalSpace,
    ) -> Self {
        let main_fn = objects::CompiledFunction {
            instructions: bytecode.instructions,
            num_locals: 0,
            num_parameters: 0,
        };
        let closure = objects::Closure {
            func: main_fn,
            ..Default::default()
        };
        let main_frame = frame::Frame::new(closure, 0);

        let mut stack_frame = frame::StackFrame::new();
        stack_frame.push(main_frame);

        Self {
            constants: bytecode.constants,
            globals,
            stack: Stack::new(),
            stack_frame,
        }
    }

    pub fn stack_top(&self) -> Option<&objects::Object> {
        self.stack.top()
    }

    pub fn last_popped_stack_elem(&self) -> &objects::Object {
        self.stack.last_popped()
    }

    pub fn run(&mut self) -> Result<()> {
        while self.stack_frame.current().borrow().pointer
            < self.stack_frame.current().borrow().instructions().0.len()
        {
            let op = {
                let ip = self.stack_frame.current().borrow().pointer;
                opcode::Opcode::try_from(
                    &self.stack_frame.current().borrow().instructions().0[ip..],
                )?
            };

            match &op {
                opcode::Opcode::Constant(constant) => {
                    let const_idx = constant.0;

                    // TODO: Rc<object::Object> ?
                    self.stack
                        .push(self.constants[usize::from(const_idx)].clone())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + constant.readsize();
                }
                opcode::Opcode::Add(_)
                | opcode::Opcode::Sub(_)
                | opcode::Opcode::Mul(_)
                | opcode::Opcode::Div(_) => {
                    self.execute_binary_operation(&op)?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + op.readsize();
                }
                opcode::Opcode::Pop(pop) => {
                    self.stack.pop();

                    self.stack_frame.current().borrow_mut().pointer += 1 + pop.readsize();
                }
                opcode::Opcode::True(t) => {
                    self.stack.push(TRUE.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + t.readsize();
                }
                opcode::Opcode::False(f) => {
                    self.stack.push(FALSE.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + f.readsize();
                }
                opcode::Opcode::Equal(_)
                | opcode::Opcode::NotEqual(_)
                | opcode::Opcode::GreaterThan(_) => {
                    self.execute_comparison(&op)?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + op.readsize();
                }
                opcode::Opcode::Bang(bang) => {
                    self.execute_bang_oeprator()?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + bang.readsize();
                }
                opcode::Opcode::Minus(minus) => {
                    self.execute_minus_operator()?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + minus.readsize();
                }
                opcode::Opcode::JumpNotTruthy(jump) => {
                    self.stack_frame.current().borrow_mut().pointer += 2;

                    let cond = self.stack.pop();
                    if !Self::is_truthy(cond) {
                        self.stack_frame.current().borrow_mut().pointer = usize::from(jump.0) - 1;
                    }

                    self.stack_frame.current().borrow_mut().pointer += 1;
                }
                opcode::Opcode::Jump(jump) => {
                    self.stack_frame.current().borrow_mut().pointer = usize::from(jump.0) - 1;

                    self.stack_frame.current().borrow_mut().pointer += 1;
                }
                opcode::Opcode::Null(null) => {
                    self.stack.push(NULL.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + null.readsize();
                }
                opcode::Opcode::GetGlobal(global) => {
                    let obj = &self.globals.0[usize::from(global.0)];
                    match obj {
                        Some(obj) => {
                            self.stack.push(obj.clone())?;
                        }
                        None => {
                            return Err(anyhow::format_err!(
                                "Bytecode error. Undefined global object. {}",
                                global
                            ))
                        }
                    }

                    self.stack_frame.current().borrow_mut().pointer += 1 + global.readsize();
                }
                opcode::Opcode::SetGlobal(global) => {
                    let poped = self.stack.pop();
                    self.globals.0[usize::from(global.0)] = Some(poped.clone());

                    self.stack_frame.current().borrow_mut().pointer += 1 + global.readsize();
                }
                opcode::Opcode::Array(arr) => {
                    let num_elements = usize::from(arr.0);
                    let array_obj = self.stack.extract_array(num_elements);
                    self.stack.push(array_obj.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + arr.readsize();
                }
                opcode::Opcode::Hash(hash) => {
                    let num_elements = usize::from(hash.0);
                    let hash_obj = self.stack.extract_hash(num_elements)?;
                    self.stack.push(hash_obj.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + hash.readsize();
                }
                opcode::Opcode::Index(index) => {
                    let idx = self.stack.pop().clone();
                    let left = self.stack.pop().clone();
                    self.execute_index_expressions(left, idx)?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + index.readsize();
                }
                opcode::Opcode::Call(call) => {
                    self.stack_frame.current().borrow_mut().pointer += call.readsize();

                    let num_args = call.0;
                    let obj = &self.stack.data[self.stack.pointer - 1 - usize::from(num_args)];
                    match obj {
                        objects::Object::Closure(cl) => {
                            if cl.func.num_parameters != num_args {
                                return Err(anyhow::format_err!(
                                    "wrong number of arguments: want={}, got={}",
                                    cl.func.num_parameters,
                                    num_args
                                ));
                            }

                            let frame = frame::Frame::new(
                                cl.clone(),
                                self.stack.pointer - usize::from(num_args),
                            );
                            let bp = frame.base_pointer;
                            self.stack_frame.push(frame);
                            self.stack.pointer = bp + usize::from(cl.func.num_locals);
                        }
                        objects::Object::Builtin(builtin) => {
                            self.stack_frame.current().borrow_mut().pointer += 1;

                            let start_p = self.stack.pointer - usize::from(num_args);
                            let args = &self.stack.data[start_p..self.stack.pointer];

                            let result = builtin.call(args);
                            self.stack.pointer = self.stack.pointer - usize::from(num_args) - 1;

                            match result {
                                Ok(result) => {
                                    if let Some(result) = result {
                                        self.stack.push(result)?;
                                    } else {
                                        self.stack.push(NULL.into())?;
                                    }
                                }
                                Err(e) => {
                                    self.stack
                                        .push(objects::Error::Standard(e.to_string()).into())?;
                                }
                            }
                        }
                        other_obj => {
                            return Err(anyhow::format_err!(
                                "calling non-function. received {}",
                                other_obj
                            ))
                        }
                    };
                }
                opcode::Opcode::ReturnValue(_) => {
                    let return_value = self.stack.pop().clone();
                    let frame = self.stack_frame.pop();
                    self.stack.pointer = frame.borrow().base_pointer - 1;

                    self.stack.push(return_value)?;

                    self.stack_frame.current().borrow_mut().pointer += 1;
                }
                opcode::Opcode::Return(_) => {
                    let frame = self.stack_frame.pop();
                    self.stack.pointer = frame.borrow().base_pointer - 1;

                    self.stack.push(NULL.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1;
                }
                opcode::Opcode::GetLocal(local) => {
                    let frame = self.stack_frame.current();
                    let p = frame.borrow().base_pointer + usize::from(local.0);
                    self.stack.push(self.stack.data[p].clone())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + local.readsize();
                }
                opcode::Opcode::SetLocal(local) => {
                    let frame = self.stack_frame.current();
                    let p = frame.borrow().base_pointer + usize::from(local.0);
                    self.stack.data[p] = self.stack.pop().clone();

                    self.stack_frame.current().borrow_mut().pointer += 1 + local.readsize();
                }
                opcode::Opcode::GetBuiltin(builtin) => {
                    let definition = builtin::Function::by_index(usize::from(builtin.0));
                    self.stack.push(definition.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + builtin.readsize();
                }
                opcode::Opcode::Closure(closure) => {
                    let constant = &self.constants[usize::from(closure.0)];
                    match constant {
                        objects::Object::CompiledFunction(func) => {
                            let free = (0..usize::from(closure.1))
                                .map(|i| {
                                    self.stack.data[self.stack.pointer - usize::from(closure.1) + i]
                                        .clone()
                                })
                                .collect::<Vec<_>>();
                            self.stack.pointer -= usize::from(closure.1);

                            let cl_obj = objects::Closure {
                                func: func.clone(),
                                free,
                            };
                            self.stack.push(cl_obj.into())?;
                        }
                        other => return Err(anyhow::format_err!("not a function: {}", other)),
                    }

                    self.stack_frame.current().borrow_mut().pointer += 1 + closure.readsize();
                }
                opcode::Opcode::GetFree(free) => {
                    self.stack.push(
                        self.stack_frame.current().borrow().cl.free[usize::from(free.0)].clone(),
                    )?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + free.readsize();
                }
                opcode::Opcode::CurrentClosure(curr_cl) => {
                    let current_closure = self.stack_frame.current().borrow().cl.clone();
                    self.stack.push(current_closure.into())?;

                    self.stack_frame.current().borrow_mut().pointer += 1 + curr_cl.readsize();
                }
            }
        }

        Ok(())
    }

    fn execute_binary_operation(&mut self, op: &opcode::Opcode) -> Result<()> {
        match self.stack.pop_pair() {
            (objects::Object::Integer(i1), objects::Object::Integer(i2)) => {
                let int = Self::execute_binary_integer_operation(op, i1.value, i2.value)?;
                self.stack.push(int.into())?;
            }
            (objects::Object::StringLit(s1), objects::Object::StringLit(s2)) => {
                let string = Self::execute_binary_string_operation(op, &s1.value, &s2.value)?;
                self.stack.push(string.into())?;
            }
            (unknown_obj1, unknown_obj2) => {
                return Err(anyhow::format_err!(
                    "unsupported types for binary operation: {} {}",
                    unknown_obj1,
                    unknown_obj2
                ))
            }
        }

        Ok(())
    }

    fn execute_binary_integer_operation(
        op: &opcode::Opcode,
        left_val: i64,
        right_val: i64,
    ) -> Result<objects::Integer> {
        let value = match op {
            opcode::Opcode::Add(_) => left_val + right_val,
            opcode::Opcode::Sub(_) => left_val - right_val,
            opcode::Opcode::Mul(_) => left_val * right_val,
            opcode::Opcode::Div(_) => left_val / right_val,
            _ => {
                return Err(anyhow::format_err!(
                    "unknown integer operator. received {}",
                    op
                ))
            }
        };

        Ok(objects::Integer { value })
    }

    fn execute_binary_string_operation(
        op: &opcode::Opcode,
        left_val: &str,
        right_val: &str,
    ) -> Result<objects::StringLit> {
        let value = match op {
            opcode::Opcode::Add(_) => left_val.to_string() + right_val,
            _ => {
                return Err(anyhow::format_err!(
                    "unknown string operator. received {}",
                    op
                ))
            }
        };

        Ok(objects::StringLit { value })
    }

    fn execute_comparison(&mut self, op: &opcode::Opcode) -> Result<()> {
        let (right, left) = self.stack.pop_pair();

        match (left, right) {
            (objects::Object::Integer(l), objects::Object::Integer(r)) => {
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
                unknown_op => {
                    return Err(anyhow::format_err!(
                        "unknown operator: {} ({} {})",
                        unknown_op,
                        l,
                        r
                    ))
                }
            },
        };

        Ok(())
    }

    fn execute_integer_comparison(
        op: &opcode::Opcode,
        left: &objects::Object,
        right: &objects::Object,
    ) -> Result<objects::Boolean> {
        match (left, right) {
            (objects::Object::Integer(l), objects::Object::Integer(r)) => match op {
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
                )),
            },
            (unknown_l, unknown_r) => Err(anyhow::format_err!(
                "expected (Integer, Integer). received ({}  {})",
                unknown_l,
                unknown_r
            )),
        }
    }

    fn native_bool_to_boolean_object(b: bool) -> objects::Boolean {
        if b {
            TRUE
        } else {
            FALSE
        }
    }

    fn execute_bang_oeprator(&mut self) -> Result<()> {
        let operand = self.stack.pop();
        match operand {
            objects::Object::Boolean(b) => {
                if b.value {
                    self.stack.push(FALSE.into())?;
                } else {
                    self.stack.push(TRUE.into())?;
                }
            }
            objects::Object::Null(_) => {
                self.stack.push(TRUE.into())?;
            }
            _other => self.stack.push(FALSE.into())?,
        };

        Ok(())
    }

    fn execute_minus_operator(&mut self) -> Result<()> {
        let operand = self.stack.pop();
        match operand {
            objects::Object::Integer(i) => {
                let int = objects::Integer { value: -i.value };
                self.stack.push(int.into())?
            }
            unknown => {
                return Err(anyhow::format_err!(
                    "unsupported type fot negation: {}",
                    unknown
                ))
            }
        };

        Ok(())
    }

    fn execute_index_expressions(
        &mut self,
        left: objects::Object,
        index: objects::Object,
    ) -> Result<()> {
        match (left, index) {
            (objects::Object::Array(arr), objects::Object::Integer(idx)) => {
                self.execute_array_index(arr, idx)?;
            }
            (objects::Object::Hash(hs), idx) => {
                self.execute_hash_index(hs, idx)?;
            }
            (l, i) => {
                return Err(anyhow::format_err!(
                    "index operator not supported: {:?}[{:?}]",
                    l,
                    i
                ))
            }
        }

        Ok(())
    }

    fn execute_array_index(
        &mut self,
        array: objects::Array,
        index: objects::Integer,
    ) -> Result<()> {
        if (0..i64::try_from(array.elements.len())?).contains(&index.value) {
            let ele = array.elements[usize::try_from(index.value)?].clone();
            self.stack.push(ele)?;
        } else {
            self.stack.push(NULL.into())?;
        }

        Ok(())
    }

    fn execute_hash_index(&mut self, hash: objects::Hash, index: objects::Object) -> Result<()> {
        let index = objects::HashableObject::try_from(index)?;

        match hash.pairs.get(&index) {
            Some(val) => self.stack.push(val.clone())?,
            None => self.stack.push(NULL.into())?,
        }

        Ok(())
    }

    fn is_truthy(obj: &objects::Object) -> bool {
        match obj {
            objects::Object::Boolean(b) => b.value,
            objects::Object::Null(_) => false,
            _other => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::compiler;
    use crate::lexer;
    use crate::parser;
    use crate::parser::ast;

    use super::*;

    #[derive(Clone)]
    enum Expected {
        Int(i64),
        Bool(bool),
        Null,
        String(String),
        IntArray(Vec<i64>),
        IntHash(Vec<(i64, i64)>),
        Err(String),
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

    impl From<&str> for Expected {
        fn from(value: &str) -> Self {
            Self::String(value.to_string())
        }
    }

    impl From<Vec<i64>> for Expected {
        fn from(value: Vec<i64>) -> Self {
            Self::IntArray(value)
        }
    }

    impl From<Vec<(i64, i64)>> for Expected {
        fn from(value: Vec<(i64, i64)>) -> Self {
            Self::IntHash(value)
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

    #[test]
    fn test_global_let_statements() {
        let tests: Tests = vec![
            ("let one = 1; one", 1),
            ("let one = 1; let two = 2; one + two", 3),
            ("let one = 1; let two = one + one; one + two", 3),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_string_expression() {
        let tests: Tests = vec![
            (r#""monkey""#, "monkey"),
            (r#""mon" + "key""#, "monkey"),
            (r#""mon" + "key" + "banana""#, "monkeybanana"),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_array_literals() {
        let tests: Tests = vec![
            ("[]", vec![]),
            ("[1, 2, 3]", vec![1, 2, 3]),
            ("[1 + 2, 3 * 4, 5 + 6]", vec![3, 12, 11]),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_hash_literals() {
        let tests: Tests = vec![
            ("{}", vec![]),
            ("{1: 2, 2: 3}", vec![(1, 2), (2, 3)]),
            ("{1 + 1: 2 * 2, 3 + 3: 4 * 4}", vec![(2, 4), (6, 16)]),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_index_expressions() {
        let tests: Tests = vec![
            ("[1, 2, 3][1]", 2),
            ("[1, 2, 3][0 + 2]", 3),
            ("[[1, 1, 1]][0][0]", 1),
            ("{1: 1, 2: 2}[1]", 1),
            ("{1: 1, 2: 2}[2]", 2),
        ]
        .into();
        run_vm_tests(tests);

        let tests: Tests = vec![
            ("[][0]", Expected::Null),
            ("[1][-1]", Expected::Null),
            ("{}[0]", Expected::Null),
            ("{1: 1}[0]", Expected::Null),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_calling_function_without_arguments() {
        let tests: Tests = vec![(
            "
                let five_plus_ten = fn() { 5 + 10; };
                five_plus_ten();
            ",
            15,
        )]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_calling_functions_without_arguments() {
        let tests: Tests = vec![
            (
                "
                    let one = fn() { 1; };
                    let two = fn() { 2; };
                    one() + two()
                ",
                3,
            ),
            (
                "
                    let a = fn() { 1 };
                    let b = fn() { a() + 1 };
                    let c = fn() { b() + 1 };
                    c();
                ",
                3,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_functions_with_return_statement() {
        let tests: Tests = vec![
            (
                "
                    let early_exit = fn() { return 99; 100; };
                    early_exit();
                ",
                99,
            ),
            (
                "
                    let early_exit = fn() { return 99; return 100; };
                    early_exit();
                ",
                99,
            ),
            (
                "
                    let early_exit = fn() { 99; return 100; };
                    early_exit();
                ",
                100,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_functions_without_return_value() {
        let tests: Tests = vec![
            (
                "
                    let no_return = fn() { };
                    no_return();
                ",
                Expected::Null,
            ),
            (
                "
                    let no_return = fn() { };
                    let no_return_two = fn() { no_return(); };
                    no_return();
                    no_return_two();
                ",
                Expected::Null,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_first_class_functions() {
        let tests: Tests = vec![
            (
                "
                    let returns_one = fn() { 1; };
                    let returns_one_returner = fn() { returns_one };
                    returns_one_returner()();
                ",
                1,
            ),
            (
                "
                    let returns_one_returner = fn() {
                        let returns_one = fn() { 1; };
                        returns_one;
                    }
                    returns_one_returner()();
                ",
                1,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_calling_functions_with_bindings() {
        let tests: Tests = vec![
            (
                "
                    let one = fn() { let one = 1; one };
                    one();
                ",
                1,
            ),
            (
                "
                    let one_and_two = fn() { let one = 1; let two = 2; one + two; };
                    one_and_two();
                ",
                3,
            ),
            (
                "
                    let one_and_two = fn() { let one = 1; let two = 2; one + two; };
                    let three_and_four = fn() { let three = 3; let four = 4; three + four; };
                    one_and_two() + three_and_four();
                ",
                10,
            ),
            (
                "
                    let first_foobar = fn() { let foobar = 50; foobar; };
                    let second_foobar = fn() { let foobar = 100; foobar; };
                    first_foobar() + second_foobar();
                ",
                150,
            ),
            (
                "
                    let global_seed = 50;
                    let minus_one = fn() {
                        let num = 1;
                        global_seed - num;
                    }
                    let minus_two = fn() {
                        let num = 2;
                        global_seed - num;
                    }
                    minus_one() + minus_two();
                ",
                97,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_calling_functions_with_arguments_and_bindings() {
        let tests: Tests = vec![
            (
                "
                    let identity = fn(a) { a; };
                    identity(4);
                ",
                4,
            ),
            (
                "
                    let sum = fn(a, b) { a + b; };
                    sum(1, 2);
                ",
                3,
            ),
            (
                "
                    let global_num = 10;
                    let sum = fn(a, b) {
                        let c = a + b;
                        c + global_num;
                    }
                    let outer = fn() {
                        sum(1, 2) + sum(3, 4) + global_num;
                    }
                    outer() + global_num;
                ",
                50,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_calling_funcitons_with_wrong_arguments() {
        let tests = vec![
            (
                "fn() { 1; }(1);",
                "wrong number of arguments: want=0, got=1",
            ),
            (
                "fn(a) { a; }();",
                "wrong number of arguments: want=1, got=0",
            ),
            (
                "fn(a, b) { a + b; }(1);",
                "wrong number of arguments: want=2, got=1",
            ),
        ];
        run_vm_err_test(tests);
    }

    #[test]
    fn test_builtin_functions() {
        let tests: Tests = vec![
            (r#"len("")"#, 0.into()),
            (r#"len("four")"#, 4.into()),
            (r#"len("hello world")"#, 11.into()),
            ("len([1, 2, 3])", 3.into()),
            ("len([])", 0.into()),
            (
                "len(1)",
                Expected::Err("argument to 'len' not supported, got Integer".into()),
            ),
            (
                r#"len("one", "two")"#,
                Expected::Err("wrong number of arguments. got=2, want=1".into()),
            ),
            (r#"puts("hello", "world")"#, Expected::Null),
            ("first([1, 2, 3])", 1.into()),
            ("first([])", Expected::Null),
            (
                "first(1)",
                Expected::Err("argument to 'first' must be Array, got Integer".into()),
            ),
            ("last([1, 2, 3])", 3.into()),
            ("last([])", Expected::Null),
            (
                "last(1)",
                Expected::Err("argument to 'last' must be Array, got Integer".into()),
            ),
            ("rest([1, 2, 3])", vec![2, 3].into()),
            ("rest([])", Expected::Null),
            (
                "rest(1)",
                Expected::Err("argument to 'rest' must be Array, got Integer".into()),
            ),
            ("push([], 1)", vec![1].into()),
            (
                "push(1, 1)",
                Expected::Err("argument to 'push' must be Array, got Integer".into()),
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_closures() {
        let tests: Tests = vec![
            (
                "
                    let new_closure = fn(a) {
                        fn() { a; };
                    };
                    let closure = new_closure(99);
                    closure();
                ",
                99,
            ),
            (
                "
                    let new_adder = fn(a, b) {
                        fn(c) { a + b + c };
                    };
                    let adder = new_adder(1, 2);
                    adder(8);
                ",
                11,
            ),
            (
                "
                    let new_adder = fn(a, b) {
                        let c = a + b;
                        fn(d) { c + d };
                    };
                    let adder = new_adder(1, 2);
                    adder(8);
                ",
                11,
            ),
            (
                "
                    let new_adder_outer = fn(a, b) {
                        let c = a + b;
                        fn(d) {
                            let e = d + c;
                            fn(f) { e + f; };
                        };
                    };
                    let new_adder_inner = new_adder_outer(1, 2);
                    let adder = new_adder_inner(3);
                    adder(8);
                ",
                14,
            ),
            (
                "
                    let a = 1;
                    let new_adder_outer = fn(b) {
                        fn(c) {
                            fn(d) { a + b + c + d; };
                        };
                    };
                    let new_adder_inner = new_adder_outer(2);
                    let adder = new_adder_inner(3);
                    adder(8);
                ",
                14,
            ),
            (
                "
                    let new_closure = fn(a, b) {
                        let one = fn() { a; };
                        let two = fn() { b; };
                        fn() { one() + two(); };
                    };
                    let closure = new_closure(9, 90);
                    closure();
                ",
                99,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_recursive_functions() {
        let tests: Tests = vec![
            (
                "
                    let count_down = fn(x) {
                        if (x == 0) {
                            return 0;
                        } else {
                            count_down(x - 1);
                        }
                    };
                    count_down(1);
                ",
                0,
            ),
            (
                "
                    let count_down = fn(x) {
                        if (x == 0) {
                            return 0;
                        } else {
                            count_down(x - 1);
                        }
                    };
                    let wrapper = fn() {
                        count_down(1);
                    };
                    wrapper();
                ",
                0,
            ),
            (
                "
                    let wrapper = fn() {
                        let count_down = fn(x) {
                            if (x == 0) {
                                return 0;
                            } else {
                                count_down(x - 1);
                            }
                        };
                        count_down(1);
                    };
                    wrapper();
                ",
                0,
            ),
        ]
        .into();
        run_vm_tests(tests);
    }

    #[test]
    fn test_recursive_fibonacci() {
        let tests: Tests = vec![(
            "
                let fibonacci = fn(x) {
                    if (x == 0) {
                        return 0;
                    } else {
                        if (x == 1) {
                            return 1;
                        } else {
                            fibonacci(x - 1) + fibonacci(x - 2);
                        }
                    }
                };
                fibonacci(15);
            ",
            610,
        )]
        .into();
        run_vm_tests(tests);
    }

    fn run_vm_err_test(tests: Vec<(&'static str, &'static str)>) {
        tests.into_iter().for_each(|(input, expected)| {
            let program = parse(input);
            let sym_table = std::rc::Rc::new(std::cell::RefCell::new(compiler::SymbolTable::new()));
            let mut constants = Default::default();
            let mut comp = compiler::Compiler::new_with_state(sym_table, &mut constants);
            if let Err(e) = comp.compile(program.into()) {
                panic!("compiler error {}: ", e);
            }
            let bytecode: bytecode::Bytecode = comp.into();

            let mut globals = Default::default();
            let mut vm = VM::new_with_globals_store(bytecode, &mut globals);
            if let Err(e) = vm.run() {
                assert_eq!(e.to_string(), expected);
            } else {
                panic!("expected VM error but resulted in none.")
            }
        });
    }

    fn run_vm_tests(tests: Tests) {
        tests.0.into_iter().for_each(|(input, expected)| {
            let program = parse(input.as_str());
            let sym_table = std::rc::Rc::new(std::cell::RefCell::new(
                compiler::SymbolTable::new_with_builtin(),
            ));
            let mut constants = Default::default();
            let mut comp = compiler::Compiler::new_with_state(sym_table, &mut constants);
            if let Err(e) = comp.compile(program.into()) {
                panic!("compiler error {}: ", e);
            }
            let bytecode: bytecode::Bytecode = comp.into();
            let debug = bytecode.clone();

            let mut globals = Default::default();
            let mut vm = VM::new_with_globals_store(bytecode, &mut globals);
            if let Err(e) = vm.run() {
                panic!("vm error: {} by {:?}", e, debug);
            }

            let stack_elem = vm.last_popped_stack_elem();

            test_object(stack_elem, &expected);
        });
    }

    fn test_object(actual: &objects::Object, expected: &Expected) {
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
            Expected::String(expected_string) => {
                test_string_object(actual, expected_string);
            }
            Expected::IntArray(expected_array) => {
                test_int_array_object(actual, expected_array);
            }
            Expected::IntHash(expected_hash) => {
                test_int_hash_object(actual.clone(), expected_hash);
            }
            Expected::Err(expected_err) => {
                test_err_object(actual, expected_err);
            }
        }
    }

    fn test_integer_object(actual: &objects::Object, expected: i64) {
        let result = match actual {
            objects::Object::Integer(int) => int,
            obj => panic!("expected Integer. received {}", obj),
        };

        assert_eq!(result.value, expected);
    }

    fn test_bool_object(actual: &objects::Object, expected: bool) {
        let result = match actual {
            objects::Object::Boolean(b) => b,
            obj => panic!("expected Boolean. received {}", obj),
        };
        assert_eq!(result.value, expected);
    }

    fn test_null_object(actual: &objects::Object) {
        match actual {
            objects::Object::Null(_) => (),
            obj => panic!("expected Null. received {}", obj),
        };
    }

    fn test_string_object(actual: &objects::Object, expected: &str) {
        match actual {
            objects::Object::StringLit(s) => {
                assert_eq!(s.value, expected);
            }
            obj => panic!("expected String. received {}", obj),
        }
    }

    fn test_int_array_object(actual: &objects::Object, expected: &[i64]) {
        match actual {
            objects::Object::Array(arr) => expected
                .iter()
                .zip(arr.elements.iter())
                .for_each(|(expected, obj)| test_integer_object(obj, *expected)),
            obj => panic!("expected Array. received {}", obj),
        }
    }

    fn test_int_hash_object(actual: objects::Object, expected: &[(i64, i64)]) {
        match actual {
            objects::Object::Hash(hash) => {
                let mut expected_hash = objects::HashPairs::new();
                expected
                    .iter()
                    .try_for_each::<_, anyhow::Result<()>>(|(key, val)| {
                        let key =
                            objects::Object::from(objects::Integer { value: *key }).try_into()?;
                        let val = objects::Integer { value: *val }.into();
                        expected_hash.insert(key, val);

                        Ok(())
                    })
                    .unwrap_or_else(|_| panic!("failed convert {:?} to HashPairs", expected));

                assert_eq!(hash.pairs, expected_hash);
            }
            obj => panic!("expected hash. received {}", obj),
        }
    }

    fn test_err_object(actual: &objects::Object, expected: &str) {
        match actual {
            objects::Object::Error(err) => match err {
                objects::Error::Standard(msg) => assert_eq!(msg, expected),
            },
            obj => panic!("expected error. received {}", obj),
        }
    }

    fn parse(input: &str) -> ast::Program {
        let l = lexer::Lexer::new(input.into());
        let mut p = parser::Parser::new(l);
        p.parse_program().unwrap()
    }
}
