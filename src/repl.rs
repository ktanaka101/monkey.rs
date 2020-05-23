use std::cell::RefCell;
use std::io;
use std::io::Write;
use std::rc::Rc;

use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::vm::env::Environment;
use crate::vm::evaluator::eval_node;
use crate::vm::object;

const PROMPT: &str = ">> ";

pub fn start() {
    let env = Rc::new(RefCell::new(Environment::new(None)));

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
                println!("{}", x);
                continue;
            }
        };

        let evaluated = eval_node(&program.into(), Rc::clone(&env));
        match evaluated {
            Ok(o) => match o {
                object::Object::Null(_) => continue,
                o => println!("{}", o),
            },
            Err(e) => {
                println!("{}", e);
                continue;
            }
        }
    }
}
