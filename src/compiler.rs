use std::cell::RefCell;
use std::rc::Rc;

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

#[derive(Debug, Clone, Default)]
struct CompilationScope {
    instructions: bytecode::Instructions,
    last_instruction: Option<EmittedInstruction>,
    prev_instruction: Option<EmittedInstruction>,
}

impl CompilationScope {
    fn new() -> Self {
        Self::default()
    }

    fn add_instructions(&mut self, instructions: &mut bytecode::Instructions) -> Pos {
        let pos_new_instruction = Pos::try_from(self.instructions.0.len()).unwrap();
        self.instructions.0.append(&mut instructions.0);
        pos_new_instruction
    }

    fn set_last_instruction(&mut self, op: opcode::Opcode, pos: Pos) {
        let prev = self.last_instruction.clone();
        let last = EmittedInstruction {
            opcode: op,
            position: pos,
        };

        self.prev_instruction = prev;
        self.last_instruction = Some(last);
    }

    fn last_instruction_is(&self, opcode: &opcode::Opcode) -> bool {
        if self.instructions.0.len() == 0 {
            return false;
        }

        match &self.last_instruction {
            Some(inst) => &inst.opcode == opcode,
            None => false,
        }
    }

    fn remove_last_pop(&mut self) -> Result<()> {
        if let Some(last_isnt) = &self.last_instruction {
            let prev = self.prev_instruction.clone();
            let new = self.instructions.0[..usize::from(last_isnt.position)].to_vec();

            self.instructions = new.into();
            self.last_instruction = prev;

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

    fn change_operand(&mut self, op_pos: Pos, operand: u16) -> Result<()> {
        let op = opcode::Opcode::try_from(&self.instructions.0[usize::from(op_pos)..])?;
        match op {
            opcode::Opcode::JumpNotTruthy(mut op) => {
                op.0 = operand;
                self.replace_instructions(op_pos, op.into());
            }
            opcode::Opcode::Jump(mut op) => {
                op.0 = operand;
                self.replace_instructions(op_pos, op.into());
            }
            _ => Err(anyhow::format_err!(
                "Expected JumpNotTruthy or Jump. received {}",
                op
            ))?,
        }

        Ok(())
    }

    fn replace_last_pop_with_return(&mut self) -> Result<()> {
        let last_pos = match &self.last_instruction {
            Some(inst) => inst.position,
            None => Err(anyhow::format_err!("uninitialized"))?,
        };
        self.replace_instructions(last_pos, opcode::ReturnValue.into());

        self.last_instruction = Some(EmittedInstruction {
            opcode: opcode::ReturnValue.into(),
            ..self.last_instruction.clone().unwrap()
        });

        Ok(())
    }
}

#[derive(Debug, Clone)]
struct CompilationScopes {
    data: Vec<Rc<RefCell<CompilationScope>>>,
    pointer: usize,
}

impl Default for CompilationScopes {
    fn default() -> Self {
        Self {
            data: vec![Rc::new(RefCell::new(CompilationScope::new()))],
            pointer: 0,
        }
    }
}

impl CompilationScopes {
    fn new() -> Self {
        Self::default()
    }

    fn push_new_scope(&mut self) {
        let scope = CompilationScope::new();
        self.data.push(Rc::new(RefCell::new(scope)));
        self.pointer += 1;
    }

    fn pop(&mut self) -> Option<Rc<RefCell<CompilationScope>>> {
        self.pointer -= 1;
        self.data.pop()
    }

    fn current(&self) -> Rc<RefCell<CompilationScope>> {
        Rc::clone(&self.data[self.pointer])
    }

    fn add_instructions(&mut self, instructions: &mut bytecode::Instructions) -> Pos {
        self.current().borrow_mut().add_instructions(instructions)
    }

    fn set_last_instruction(&mut self, op: opcode::Opcode, pos: Pos) {
        self.current().borrow_mut().set_last_instruction(op, pos);
    }

    fn last_instruction_is(&self, opcode: &opcode::Opcode) -> bool {
        self.current().borrow().last_instruction_is(opcode)
    }

    fn remove_last_pop(&mut self) -> Result<()> {
        self.current().borrow_mut().remove_last_pop()
    }

    fn replace_instructions(&mut self, pos: Pos, new_instructions: bytecode::Instructions) {
        self.current()
            .borrow_mut()
            .replace_instructions(pos, new_instructions);
    }

    fn change_operand(&mut self, op_pos: Pos, operand: u16) -> Result<()> {
        self.current().borrow_mut().change_operand(op_pos, operand)
    }

    fn replace_last_pop_with_return(&mut self) -> Result<()> {
        self.current().borrow_mut().replace_last_pop_with_return()
    }
}

#[derive(Debug)]
pub struct Compiler<'a> {
    constants: &'a mut Vec<object::Object>,
    symbol_table: Rc<RefCell<symbol_table::SymbolTable>>,
    scopes: CompilationScopes,
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
                    let symbol = {
                        let table = Rc::clone(&self.symbol_table);
                        let mut table = table.borrow_mut();
                        table.define(l.name.value)
                    };

                    self.compile(l.value.into())?;

                    match &*symbol.borrow() {
                        symbol_table::Symbol::Global { index, .. } => {
                            let op = opcode::SetGlobal(*index).into();
                            self.emit(op);
                        }
                        symbol_table::Symbol::Local { index, .. } => {
                            let op = opcode::SetLocal(*index).into();
                            self.emit(op);
                        }
                        symbol_table::Symbol::Builtin { .. } => unreachable!(),
                        symbol_table::Symbol::Free { .. } => unreachable!(),
                        symbol_table::Symbol::Function { .. } => unreachable!(),
                    };
                }
                ast::Stmt::Return(r) => {
                    self.compile(r.return_value.into())?;
                    self.emit(opcode::ReturnValue.into());
                }
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

                    if self.scopes.last_instruction_is(&opcode::Pop.into()) {
                        self.scopes.remove_last_pop()?;
                    }

                    let jump_pos = self.emit(opcode::Jump(9999).into());
                    {
                        let len = self.scopes.current().borrow().instructions.0.len();
                        self.scopes
                            .change_operand(jump_not_truthy_pos, u16::try_from(len)?)?;
                    }

                    if let Some(alternative) = expr.alternative {
                        self.compile(ast::Stmt::from(alternative).into())?;
                        if self.scopes.last_instruction_is(&opcode::Pop.into()) {
                            self.scopes.remove_last_pop()?;
                        }
                    } else {
                        self.emit(opcode::Null.into());
                    }

                    {
                        let len = self.scopes.current().borrow().instructions.0.len();
                        self.scopes.change_operand(jump_pos, u16::try_from(len)?)?;
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
                ast::Expr::StringLit(s) => {
                    let s = object::StringLit { value: s.value };
                    let op = opcode::Constant::from(self.add_constant(s.into()));
                    self.emit(op.into());
                }
                ast::Expr::Identifier(id) => {
                    let table = Rc::clone(&self.symbol_table);
                    let mut table = table.borrow_mut();
                    let symbol = table.resolve(&id.value);

                    match symbol {
                        Some(symbol) => {
                            self.load_symbol(&*symbol.borrow());
                        }
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
                ast::Expr::Hash(hash) => {
                    let hash_len = u16::try_from(hash.pairs.len() * 2)?;
                    hash.pairs.into_iter().try_for_each(|pair| {
                        self.compile(pair.key.into())?;
                        self.compile(pair.value.into())
                    })?;
                    self.emit(opcode::Hash(hash_len).into());
                }
                ast::Expr::Index(index) => {
                    self.compile((*index.left).into())?;
                    self.compile((*index.index).into())?;
                    self.emit(opcode::Index.into());
                }
                ast::Expr::Function(func) => {
                    self.enter_scope();

                    if !func.name.is_empty() {
                        self.symbol_table
                            .borrow_mut()
                            .define_function_name(func.name);
                    }

                    let num_parameters = u8::try_from(func.params.len())?;

                    func.params.into_iter().for_each(|param| {
                        self.symbol_table.borrow_mut().define(param.value);
                    });

                    self.compile(ast::Stmt::from(func.body).into())?;
                    if self.scopes.last_instruction_is(&opcode::Pop.into()) {
                        self.scopes.replace_last_pop_with_return()?;
                    }
                    if !self.scopes.last_instruction_is(&opcode::ReturnValue.into()) {
                        self.emit(opcode::Return.into());
                    }

                    let free_symbols = self.symbol_table.borrow().free_symbols.clone();
                    let num_locals = self.symbol_table.borrow().num_definitions;
                    let scope = self.leave_scope()?;
                    let instructions = scope.borrow().instructions.clone();

                    free_symbols.iter().for_each(|sym| {
                        self.load_symbol(&*sym.borrow());
                    });

                    let compiled_func = object::CompiledFunction {
                        instructions,
                        num_locals,
                        num_parameters,
                    };
                    let constant = self.add_constant(compiled_func.into());
                    self.emit(opcode::Closure(constant, u8::try_from(free_symbols.len())?).into());
                }
                ast::Expr::Call(call) => {
                    self.compile((*call.func).into())?;
                    let arg_len = u8::try_from(call.args.len())?;
                    call.args
                        .into_iter()
                        .try_for_each(|arg| self.compile(arg.into()))?;
                    self.emit(opcode::Call(arg_len).into());
                }
                _ => unimplemented!(),
            },
        }
        Ok(())
    }

    pub fn current_instructions(&self) -> bytecode::Instructions {
        self.scopes.current().borrow().instructions.clone()
    }

    fn add_constant(&mut self, obj: object::Object) -> Pos {
        self.constants.push(obj);
        Pos::try_from(self.constants.len()).unwrap() - 1
    }

    fn emit(&mut self, op: opcode::Opcode) -> Pos {
        let mut ins: bytecode::Instructions = op.to_bytes().into();
        let pos = self.scopes.add_instructions(&mut ins);

        self.scopes.set_last_instruction(op, pos);

        pos
    }

    fn enter_scope(&mut self) {
        self.scopes.push_new_scope();

        self.symbol_table = {
            let table = Rc::clone(&self.symbol_table);
            Rc::new(RefCell::new(SymbolTable::new_enclosed(table)))
        };
    }

    fn leave_scope(&mut self) -> Result<Rc<RefCell<CompilationScope>>> {
        let scope = self.scopes.pop();
        let scope = scope.ok_or(anyhow::format_err!("Empty scope"))?;

        let table = self.symbol_table.borrow_mut().outer.take();
        if let Some(table) = table {
            self.symbol_table = table;
        }

        Ok(scope)
    }

    fn load_symbol(&mut self, symbol: &symbol_table::Symbol) {
        let symbol = match symbol {
            symbol_table::Symbol::Global { index, .. } => opcode::GetGlobal(*index).into(),
            symbol_table::Symbol::Local { index, .. } => opcode::GetLocal(*index).into(),
            symbol_table::Symbol::Builtin { index, .. } => opcode::GetBuiltin(*index).into(),
            symbol_table::Symbol::Free { index, .. } => opcode::GetFree(*index).into(),
            symbol_table::Symbol::Function { .. } => opcode::CurrentClosure.into(),
        };
        self.emit(symbol);
    }
}

impl<'a> Compiler<'a> {
    pub fn new_with_state(
        sym_table: Rc<RefCell<symbol_table::SymbolTable>>,
        constants: &'a mut Vec<object::Object>,
    ) -> Self {
        Self {
            symbol_table: sym_table,
            constants: constants,
            scopes: CompilationScopes::new(),
        }
    }
}

impl From<Compiler<'_>> for crate::vm::bytecode::Bytecode {
    fn from(value: Compiler) -> Self {
        Self {
            instructions: value.current_instructions(),
            constants: value.constants.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer;
    use crate::parser;

    use super::*;

    enum Expected {
        Int(i64),
        String(String),
        Function(bytecode::Instructions),
    }

    impl From<i64> for Expected {
        fn from(value: i64) -> Self {
            Expected::Int(value)
        }
    }

    impl From<&str> for Expected {
        fn from(value: &str) -> Self {
            Expected::String(value.into())
        }
    }

    impl From<Vec<opcode::Opcode>> for Expected {
        fn from(value: Vec<opcode::Opcode>) -> Self {
            Expected::Function(value.into())
        }
    }

    struct Tests(Vec<(&'static str, Vec<Expected>, bytecode::Instructions)>);

    impl<T, U> From<Vec<(&'static str, Vec<T>, U)>> for Tests
    where
        T: Into<Expected>,
        U: Into<bytecode::Instructions>,
    {
        fn from(value: Vec<(&'static str, Vec<T>, U)>) -> Self {
            Tests(
                value
                    .into_iter()
                    .map(|val| {
                        (
                            val.0,
                            val.1.into_iter().map(|v| v.into()).collect::<Vec<_>>(),
                            val.2.into(),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
        }
    }

    #[test]
    fn test_compiler() {
        let tests = vec![(
            "1 + 2",
            vec![1, 2],
            Vec::<opcode::Opcode>::from(vec![
                opcode::Constant(0).into(),
                opcode::Constant(1).into(),
                opcode::Add.into(),
                opcode::Pop.into(),
            ]),
        )]
        .into();

        run_compiler_tests(tests);
    }

    #[test]
    fn test_integer_arithmetic() {
        let tests: Tests = vec![
            (
                "1 + 2",
                vec![1, 2],
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Add.into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "1 - 2",
                vec![1, 2],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Sub.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "1 * 2",
                vec![1, 2],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Mul.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "1 / 2",
                vec![1, 2],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Div.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "1; 2",
                vec![1, 2],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Pop.into(),
                    opcode::Constant(1).into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "-1",
                vec![1],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Minus.into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();

        run_compiler_tests(tests);
    }

    #[test]
    fn test_boolean_expressions() {
        let tests: Tests = vec![
            (
                "true",
                vec![],
                Vec::<opcode::Opcode>::from(vec![opcode::True.into(), opcode::Pop.into()]),
            ),
            (
                "false",
                vec![],
                vec![opcode::False.into(), opcode::Pop.into()],
            ),
            (
                "1 > 2",
                vec![1, 2],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::GreaterThan.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "1 < 2",
                vec![2, 1],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::GreaterThan.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "1 == 2",
                vec![1, 2],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Equal.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "1 != 2",
                vec![1, 2],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::NotEqual.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "true == false",
                vec![],
                vec![
                    opcode::True.into(),
                    opcode::False.into(),
                    opcode::Equal.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "true != false",
                vec![],
                vec![
                    opcode::True.into(),
                    opcode::False.into(),
                    opcode::NotEqual.into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "!true",
                vec![],
                vec![opcode::True.into(), opcode::Bang.into(), opcode::Pop.into()],
            ),
            (
                "!false",
                vec![],
                vec![
                    opcode::False.into(),
                    opcode::Bang.into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();

        run_compiler_tests(tests);
    }

    #[test]
    fn test_conditionals() {
        let tests: Tests = vec![
            (
                "if (true) { 10 }; 3333;",
                vec![10, 3333],
                Vec::<opcode::Opcode>::from(vec![
                    opcode::True.into(),
                    opcode::JumpNotTruthy(10).into(),
                    opcode::Constant(0).into(),
                    opcode::Jump(11).into(),
                    opcode::Null.into(),
                    opcode::Pop.into(),
                    opcode::Constant(1).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "if (true) { 10 } else { 20 }; 3333;",
                vec![10, 20, 3333],
                vec![
                    opcode::True.into(),
                    opcode::JumpNotTruthy(10).into(),
                    opcode::Constant(0).into(),
                    opcode::Jump(13).into(),
                    opcode::Constant(1).into(),
                    opcode::Pop.into(),
                    opcode::Constant(2).into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_global_let_statements() {
        let tests: Tests = vec![
            (
                "
                let one = 1;
                let two = 2;
                ",
                vec![1, 2],
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Constant(0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::Constant(1).into(),
                    opcode::SetGlobal(1).into(),
                ]),
            ),
            (
                "
                let one = 1;
                one;
                ",
                vec![1],
                vec![
                    opcode::Constant(0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "
                let one = 1;
                let two = one;
                two;
                ",
                vec![1],
                vec![
                    opcode::Constant(0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::SetGlobal(1).into(),
                    opcode::GetGlobal(1).into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();

        run_compiler_tests(tests);
    }

    #[test]
    fn test_string_expressions() {
        let tests: Tests = vec![
            (
                r#""monkey""#,
                vec!["monkey"],
                Vec::<opcode::Opcode>::from(vec![opcode::Constant(0).into(), opcode::Pop.into()]),
            ),
            (
                r#""mon" + "key""#,
                vec!["mon", "key"],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Add.into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();

        run_compiler_tests(tests);
    }

    #[test]
    fn test_array_literals() {
        let tests: Tests = vec![
            (
                "[]",
                vec![],
                Vec::<opcode::Opcode>::from(vec![opcode::Array(0).into(), opcode::Pop.into()]),
            ),
            (
                "[1, 2, 3]",
                vec![1, 2, 3],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Constant(2).into(),
                    opcode::Array(3).into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "[1 + 2, 3 - 4, 5 * 6]",
                vec![1, 2, 3, 4, 5, 6],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Add.into(),
                    opcode::Constant(2).into(),
                    opcode::Constant(3).into(),
                    opcode::Sub.into(),
                    opcode::Constant(4).into(),
                    opcode::Constant(5).into(),
                    opcode::Mul.into(),
                    opcode::Array(3).into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_hash_literals() {
        let tests: Tests = vec![
            (
                "{}",
                vec![],
                Vec::<opcode::Opcode>::from(vec![opcode::Hash(0).into(), opcode::Pop.into()]),
            ),
            (
                "{1: 2, 3: 4, 5: 6}",
                vec![1, 2, 3, 4, 5, 6],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Constant(2).into(),
                    opcode::Constant(3).into(),
                    opcode::Constant(4).into(),
                    opcode::Constant(5).into(),
                    opcode::Hash(6).into(),
                    opcode::Pop.into(),
                ],
            ),
            (
                "{1: 2 + 3, 4: 5 * 6}",
                vec![1, 2, 3, 4, 5, 6],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Constant(2).into(),
                    opcode::Add.into(),
                    opcode::Constant(3).into(),
                    opcode::Constant(4).into(),
                    opcode::Constant(5).into(),
                    opcode::Mul.into(),
                    opcode::Hash(4).into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_index_expressions() {
        let tests: Tests = vec![
            (
                "[1, 2, 3][1 + 1]",
                vec![1, 2, 3, 1, 1],
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Constant(2).into(),
                    opcode::Array(3).into(),
                    opcode::Constant(3).into(),
                    opcode::Constant(4).into(),
                    opcode::Add.into(),
                    opcode::Index.into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "{1: 2}[2 - 1]",
                vec![1, 2, 2, 1],
                vec![
                    opcode::Constant(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Hash(2).into(),
                    opcode::Constant(2).into(),
                    opcode::Constant(3).into(),
                    opcode::Sub.into(),
                    opcode::Index.into(),
                    opcode::Pop.into(),
                ],
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_function() {
        let tests: Tests = vec![
            (
                "fn() { return 5 + 10 }",
                Vec::<Expected>::from(vec![
                    5.into(),
                    10.into(),
                    Vec::<opcode::Opcode>::from(vec![
                        opcode::Constant(0).into(),
                        opcode::Constant(1).into(),
                        opcode::Add.into(),
                        opcode::ReturnValue.into(),
                    ])
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(2, 0).into(), opcode::Pop.into()]),
            ),
            (
                "fn() { 5 + 10 }",
                Vec::<Expected>::from(vec![
                    5.into(),
                    10.into(),
                    Vec::<opcode::Opcode>::from(vec![
                        opcode::Constant(0).into(),
                        opcode::Constant(1).into(),
                        opcode::Add.into(),
                        opcode::ReturnValue.into(),
                    ])
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(2, 0).into(), opcode::Pop.into()]),
            ),
            (
                "fn() { 1; 2 }",
                Vec::<Expected>::from(vec![
                    1.into(),
                    2.into(),
                    Vec::<opcode::Opcode>::from(vec![
                        opcode::Constant(0).into(),
                        opcode::Pop.into(),
                        opcode::Constant(1).into(),
                        opcode::ReturnValue.into(),
                    ])
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(2, 0).into(), opcode::Pop.into()]),
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_compiler_scopes() {
        let sym_table = Default::default();
        let mut constants = Default::default();
        let mut compiler = Compiler::new_with_state(sym_table, &mut constants);
        assert_eq!(compiler.scopes.pointer, 0);
        assert_eq!(compiler.scopes.data.len(), 1);

        compiler.emit(opcode::Mul.into());
        assert_eq!(compiler.scopes.pointer, 0);
        assert_eq!(compiler.scopes.data[0].borrow().instructions.0.len(), 1);

        compiler.enter_scope();
        assert_eq!(compiler.scopes.pointer, 1);
        assert_eq!(compiler.scopes.data.len(), 2);
        assert_eq!(compiler.scopes.data[1].borrow().instructions.0.len(), 0);

        compiler.emit(opcode::Sub.into());
        assert_eq!(compiler.scopes.pointer, 1);
        assert_eq!(compiler.scopes.data[0].borrow().instructions.0.len(), 1);
        assert_eq!(compiler.scopes.data[1].borrow().instructions.0.len(), 1);

        let last = &compiler.scopes.data[compiler.scopes.pointer];
        let last = last.borrow().last_instruction.clone().unwrap();
        match &last.opcode {
            opcode::Opcode::Sub(_) => (),
            op => panic!("expected opcode::Sub. received {}", op),
        }

        compiler.leave_scope().unwrap();
        assert_eq!(compiler.scopes.pointer, 0);

        compiler.emit(opcode::Add.into());
        assert_eq!(compiler.scopes.data.len(), 1);
        assert_eq!(
            compiler.scopes.data[compiler.scopes.pointer]
                .borrow()
                .instructions
                .0
                .len(),
            2
        );

        let last = &compiler.scopes.data[compiler.scopes.pointer];
        let last = last.borrow().last_instruction.clone().unwrap();
        match &last.opcode {
            opcode::Opcode::Add(_) => (),
            op => panic!("expected opcode::Add. received {}", op),
        }

        let prev = &compiler.scopes.data[compiler.scopes.pointer];
        let prev = prev.borrow().prev_instruction.clone().unwrap();
        match &prev.opcode {
            opcode::Opcode::Mul(_) => (),
            op => panic!("expected opcode::Mul. received {}", op),
        }
    }

    #[test]
    fn test_functions_without_return_value() {
        let tests: Tests = vec![(
            "fn() { }",
            vec![vec![opcode::Return.into()]],
            Vec::<opcode::Opcode>::from(vec![opcode::Closure(0, 0).into(), opcode::Pop.into()]),
        )]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_function_calls() {
        let tests: Tests = vec![
            (
                "fn() { 24 }()",
                Vec::<Expected>::from(vec![
                    24.into(),
                    vec![opcode::Constant(0).into(), opcode::ReturnValue.into()].into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(1, 0).into(),
                    opcode::Call(0).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "
                    let no_arg = fn() { 24 };
                    no_arg();
                ",
                Vec::<Expected>::from(vec![
                    24.into(),
                    vec![opcode::Constant(0).into(), opcode::ReturnValue.into()].into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(1, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Call(0).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "
                    let one_arg = fn(a) { };
                    one_arg(24);
                ",
                Vec::<Expected>::from(vec![vec![opcode::Return.into()].into(), 24.into()]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(0, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Call(1).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "
                    let many_arg = fn(a, b, c) { };
                    many_arg(24, 25, 26);
                ",
                Vec::<Expected>::from(vec![
                    vec![opcode::Return.into()].into(),
                    24.into(),
                    25.into(),
                    26.into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(0, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Constant(2).into(),
                    opcode::Constant(3).into(),
                    opcode::Call(3).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "
                    let one_arg = fn(a) { a };
                    one_arg(24);
                ",
                Vec::<Expected>::from(vec![
                    vec![opcode::GetLocal(0).into(), opcode::ReturnValue.into()].into(),
                    24.into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(0, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Call(1).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "
                    let many_arg = fn(a, b, c) { a; b; c; };
                    many_arg(24, 25, 26);
                ",
                Vec::<Expected>::from(vec![
                    vec![
                        opcode::GetLocal(0).into(),
                        opcode::Pop.into(),
                        opcode::GetLocal(1).into(),
                        opcode::Pop.into(),
                        opcode::GetLocal(2).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    24.into(),
                    25.into(),
                    26.into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(0, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Constant(1).into(),
                    opcode::Constant(2).into(),
                    opcode::Constant(3).into(),
                    opcode::Call(3).into(),
                    opcode::Pop.into(),
                ]),
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_let_statement_scopes() {
        let tests: Tests = vec![
            (
                "
                    let num = 55;
                    fn() { num }
                ",
                Vec::<Expected>::from(vec![
                    55.into(),
                    vec![opcode::GetGlobal(0).into(), opcode::ReturnValue.into()].into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Constant(0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::Closure(1, 0).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "
                    fn() { 
                        let num = 55;
                        num
                    }
                ",
                Vec::<Expected>::from(vec![
                    55.into(),
                    vec![
                        opcode::Constant(0).into(),
                        opcode::SetLocal(0).into(),
                        opcode::GetLocal(0).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(1, 0).into(), opcode::Pop.into()]),
            ),
            (
                "
                    fn() { 
                        let a = 55;
                        let b = 77;
                        a + b
                    }
                ",
                Vec::<Expected>::from(vec![
                    55.into(),
                    77.into(),
                    vec![
                        opcode::Constant(0).into(),
                        opcode::SetLocal(0).into(),
                        opcode::Constant(1).into(),
                        opcode::SetLocal(1).into(),
                        opcode::GetLocal(0).into(),
                        opcode::GetLocal(1).into(),
                        opcode::Add.into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(2, 0).into(), opcode::Pop.into()]),
            ),
            (
                "
                    let one = fn() { let one = 1; one };
                    one();
                ",
                Vec::<Expected>::from(vec![
                    1.into(),
                    vec![
                        opcode::Constant(0).into(),
                        opcode::SetLocal(0).into(),
                        opcode::GetLocal(0).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(1, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Call(0).into(),
                    opcode::Pop.into(),
                ]),
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_builtins() {
        let tests: Tests = vec![
            (
                "
                len([]);
                push([], 1);
            ",
                Vec::<Expected>::from(vec![1.into()]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::GetBuiltin(0).into(),
                    opcode::Array(0).into(),
                    opcode::Call(1).into(),
                    opcode::Pop.into(),
                    opcode::GetBuiltin(4).into(),
                    opcode::Array(0).into(),
                    opcode::Constant(0).into(),
                    opcode::Call(2).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "fn() { len([]) }",
                Vec::<Expected>::from(vec![vec![
                    opcode::GetBuiltin(0).into(),
                    opcode::Array(0).into(),
                    opcode::Call(1).into(),
                    opcode::ReturnValue.into(),
                ]
                .into()]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(0, 0).into(), opcode::Pop.into()]),
            ),
            (
                r#"len("")"#,
                Vec::<Expected>::from(vec!["".into()]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::GetBuiltin(0).into(),
                    opcode::Constant(0).into(),
                    opcode::Call(1).into(),
                    opcode::Pop.into(),
                ]),
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_closures() {
        let tests: Tests = vec![
            (
                "
                    fn(a) {
                        fn(b) {
                            a + b
                        }
                    }
                ",
                Vec::<Expected>::from(vec![
                    vec![
                        opcode::GetFree(0).into(),
                        opcode::GetLocal(0).into(),
                        opcode::Add.into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    vec![
                        opcode::GetLocal(0).into(),
                        opcode::Closure(0, 1).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(1, 0).into(), opcode::Pop.into()]),
            ),
            (
                "
                    fn(a) {
                        fn(b) {
                            fn(c) {
                                a + b + c
                            }
                        }
                    }
                ",
                Vec::<Expected>::from(vec![
                    vec![
                        opcode::GetFree(0).into(),
                        opcode::GetFree(1).into(),
                        opcode::Add.into(),
                        opcode::GetLocal(0).into(),
                        opcode::Add.into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    vec![
                        opcode::GetFree(0).into(),
                        opcode::GetLocal(0).into(),
                        opcode::Closure(0, 2).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    vec![
                        opcode::GetLocal(0).into(),
                        opcode::Closure(1, 1).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![opcode::Closure(2, 0).into(), opcode::Pop.into()]),
            ),
            (
                "
                    let global = 55;

                    fn() {
                        let a = 66;

                        fn() {
                            let b = 77;

                            fn() {
                                let c = 88;

                                global + a + b + c;
                            }
                        }
                    }
                ",
                Vec::<Expected>::from(vec![
                    55.into(),
                    66.into(),
                    77.into(),
                    88.into(),
                    vec![
                        opcode::Constant(3).into(),
                        opcode::SetLocal(0).into(),
                        opcode::GetGlobal(0).into(),
                        opcode::GetFree(0).into(),
                        opcode::Add.into(),
                        opcode::GetFree(1).into(),
                        opcode::Add.into(),
                        opcode::GetLocal(0).into(),
                        opcode::Add.into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    vec![
                        opcode::Constant(2).into(),
                        opcode::SetLocal(0).into(),
                        opcode::GetFree(0).into(),
                        opcode::GetLocal(0).into(),
                        opcode::Closure(4, 2).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    vec![
                        opcode::Constant(1).into(),
                        opcode::SetLocal(0).into(),
                        opcode::GetLocal(0).into(),
                        opcode::Closure(5, 1).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Constant(0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::Closure(6, 0).into(),
                    opcode::Pop.into(),
                ]),
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    #[test]
    fn test_recursive_functions() {
        let tests: Tests = vec![
            (
                "
                    let count_down = fn(x) { count_down(x - 1); };
                    count_down(1);
                ",
                Vec::<Expected>::from(vec![
                    1.into(),
                    vec![
                        opcode::CurrentClosure.into(),
                        opcode::GetLocal(0).into(),
                        opcode::Constant(0).into(),
                        opcode::Sub.into(),
                        opcode::Call(1).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    1.into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(1, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Constant(2).into(),
                    opcode::Call(1).into(),
                    opcode::Pop.into(),
                ]),
            ),
            (
                "
                    let wrapper = fn() {
                        let count_down = fn(x) { count_down(x - 1); };
                        count_down(1);
                    }
                    wrapper();
                ",
                Vec::<Expected>::from(vec![
                    1.into(),
                    vec![
                        opcode::CurrentClosure.into(),
                        opcode::GetLocal(0).into(),
                        opcode::Constant(0).into(),
                        opcode::Sub.into(),
                        opcode::Call(1).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                    1.into(),
                    vec![
                        opcode::Closure(1, 0).into(),
                        opcode::SetLocal(0).into(),
                        opcode::GetLocal(0).into(),
                        opcode::Constant(2).into(),
                        opcode::Call(1).into(),
                        opcode::ReturnValue.into(),
                    ]
                    .into(),
                ]),
                Vec::<opcode::Opcode>::from(vec![
                    opcode::Closure(3, 0).into(),
                    opcode::SetGlobal(0).into(),
                    opcode::GetGlobal(0).into(),
                    opcode::Call(0).into(),
                    opcode::Pop.into(),
                ]),
            ),
        ]
        .into();
        run_compiler_tests(tests);
    }

    fn run_compiler_tests(tests: Tests) {
        tests
            .0
            .into_iter()
            .for_each(|(input, expected_constants, expected_instructure)| {
                let program = parse_test_input(input);
                let sym_table = Rc::new(RefCell::new(SymbolTable::new_with_builtin()));
                let mut constants = Default::default();
                let mut compiler = Compiler::new_with_state(sym_table, &mut constants);
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
            (vec![opcode::Hash(65534).into()], "0000 Hash 65534¥n"),
            (vec![opcode::Index.into()], "0000 Index¥n"),
            (vec![opcode::Call(254).into()], "0000 Call 254¥n"),
            (vec![opcode::ReturnValue.into()], "0000 ReturnValue¥n"),
            (vec![opcode::Return.into()], "0000 Return¥n"),
            (vec![opcode::GetLocal(254).into()], "0000 GetLocal 254¥n"),
            (vec![opcode::SetLocal(254).into()], "0000 SetLocal 254¥n"),
            (
                vec![opcode::GetBuiltin(254).into()],
                "0000 GetBuiltin 254¥n",
            ),
            (
                vec![opcode::Closure(65534, 254).into()],
                "0000 Closure 65534 254¥n",
            ),
            (vec![opcode::GetFree(254).into()], "0000 GetFree 254¥n"),
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

    fn test_constants(actual: Vec<object::Object>, expected: Vec<Expected>) {
        actual
            .into_iter()
            .zip(expected)
            .for_each(|(input, expected)| match expected {
                Expected::Int(i) => {
                    test_integer_object(input, i);
                }
                Expected::String(s) => test_string_object(input, s.as_str()),
                Expected::Function(f) => test_compiled_function_object(input, f),
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

    fn test_compiled_function_object(actual: object::Object, expected: bytecode::Instructions) {
        match actual {
            object::Object::CompiledFunction(f) => test_instructions(f.instructions, expected),
            o => panic!("expected object::CompiledFunction. received {}", o),
        }
    }

    fn parse_test_input(input: &str) -> ast::Program {
        let l = lexer::Lexer::new(input.into());
        let mut p = parser::Parser::new(l);
        p.parse_program().unwrap()
    }
}
