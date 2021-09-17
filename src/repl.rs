use std::cell::RefCell;
use std::io;
use std::io::Write;
use std::rc::Rc;

use crate::compiler;
use crate::evaluator::env::Environment;
use crate::evaluator::objects;
use crate::evaluator::{define_macros, eval_node, expand_macros};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::vm;

const PROMPT: &str = ">> ";

pub enum Executer {
    VM,
    Evaluator,
}

pub fn start(executer: Executer) {
    match executer {
        Executer::VM => start_vm(),
        Executer::Evaluator => start_evaluator(),
    }
}

fn start_vm() {
    let mut constants: Vec<objects::Object> = vec![];
    let mut globals: vm::GlobalSpace = vm::GlobalSpace::new();
    let symbol_table = std::rc::Rc::new(std::cell::RefCell::new(
        compiler::SymbolTable::new_with_builtin(),
    ));

    loop {
        print!("{}", PROMPT);
        io::stdout().flush().unwrap();

        let mut line = String::new();
        if io::stdin().read_line(&mut line).is_err() || line == "\n" {
            continue;
        }

        let lexer = Lexer::new(line);
        let mut parser = Parser::new(lexer);

        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(x) => {
                println!("Parse error: {}", x);
                continue;
            }
        };

        let mut comp = compiler::Compiler::new_with_state(Rc::clone(&symbol_table), &mut constants);
        if let Err(e) = comp.compile(program.into()) {
            println!("Woops! Compilation failed: \n {}", e);
            continue;
        }

        let bytecode: vm::bytecode::Bytecode = comp.into();
        let mut machine = vm::VM::new_with_globals_store(bytecode, &mut globals);
        if let Err(e) = machine.run() {
            println!("Woops! Executing bytecode failed:\n {}", e);
            continue;
        }

        let stack = machine.last_popped_stack_elem();
        println!("{}", stack);
    }
}

fn start_evaluator() {
    let env = Rc::new(RefCell::new(Environment::new(None)));
    let macro_env = Rc::new(RefCell::new(Environment::new(None)));

    loop {
        print!("{}", PROMPT);
        io::stdout().flush().unwrap();

        let mut line = String::new();
        if io::stdin().read_line(&mut line).is_err() || line == "\n" {
            continue;
        }

        let lexer = Lexer::new(line);
        let mut parser = Parser::new(lexer);

        let mut program = match parser.parse_program() {
            Ok(p) => p,
            Err(x) => {
                println!("Parse error: {}", x);
                continue;
            }
        };

        let res = define_macros(&mut program, Rc::clone(&macro_env));
        if let Err(e) = res {
            println!("Define macro error: {}", e);
            continue;
        }

        let expanded = match expand_macros(program.into(), Rc::clone(&macro_env)) {
            Ok(expanded) => expanded,
            Err(e) => {
                println!("Expand macro error: {}", e);
                continue;
            }
        };

        let evaluated = eval_node(&expanded, Rc::clone(&env));
        match evaluated {
            Ok(o) => match o {
                objects::Object::Null(_) => continue,
                o => println!("{}", o),
            },
            Err(e) => {
                println!("Eval error: {}", e);
                continue;
            }
        }
    }
}
