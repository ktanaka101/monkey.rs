use std::cell::RefCell;
use std::rc::Rc;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use monkey::compiler;
use monkey::evaluator;
use monkey::evaluator::object;
use monkey::lexer;
use monkey::parser;
use monkey::vm;

fn run_vm(input: String) -> object::Object {
    let mut constants: Vec<object::Object> = vec![];
    let mut globals: vm::GlobalSpace = Default::default();
    let symbol_table = Rc::new(RefCell::new(compiler::SymbolTable::new_with_builtin()));

    let lexer = lexer::Lexer::new(input);
    let mut parser = parser::Parser::new(lexer);

    let program = parser.parse_program().unwrap();

    let mut comp = compiler::Compiler::new_with_state(Rc::clone(&symbol_table), &mut constants);
    comp.compile(program.into()).unwrap();

    let bytecode: vm::bytecode::Bytecode = comp.into();
    let mut machine = vm::VM::new_with_globals_store(bytecode, &mut globals);
    machine.run().unwrap();

    machine.last_popped_stack_elem().clone()
}

fn run_evaluator(input: String) -> object::Object {
    let env = Rc::new(RefCell::new(evaluator::env::Environment::new(None)));
    let lexer = lexer::Lexer::new(input);
    let mut parser = parser::Parser::new(lexer);
    let program = parser.parse_program().unwrap();

    let evaluated = evaluator::eval_node(&program.into(), env);
    evaluated.unwrap()
}

const INPUT1: &'static str = "
    let fibonacci = fn(x) {
        if (x == 0) {
            0
        } else {
            if (x == 1) {
                return 1;
            } else {
                fibonacci(x - 1) + fibonacci(x - 2);
            }
        }
    };
    fibonacci(5);
";

const INPUT2: &'static str = "
    let fibonacci = fn(x) {
        if (x == 0) {
            0
        } else {
            if (x == 1) {
                return 1;
            } else {
                fibonacci(x - 1) + fibonacci(x - 2);
            }
        }
    };
    fibonacci(20);
";

const INPUT3: &'static str = "
    let fibonacci = fn(x) {
        if (x == 0) {
            0
        } else {
            if (x == 1) {
                return 1;
            } else {
                fibonacci(x - 1) + fibonacci(x - 2);
            }
        }
    };
    fibonacci(35);
";

fn bench_fibs(c: &mut Criterion) {
    let mut group = c.benchmark_group("Fibonacci");
    for (input, p) in [(INPUT1, 5), (INPUT2, 20), (INPUT3, 35)].iter() {
        group.bench_with_input(BenchmarkId::new("Evaluator", p), input, |b, input| {
            b.iter(|| run_evaluator(black_box(input.to_string())))
        });
        group.bench_with_input(BenchmarkId::new("VM", p), input, |b, input| {
            b.iter(|| run_vm(black_box(input.to_string())))
        });
    }
    group.finish();
}

criterion_group!(benches, bench_fibs);
criterion_main!(benches);
