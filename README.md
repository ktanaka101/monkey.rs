# monkey.rs

## Summury

We can learn how to make an interpreter and a compiler-vm in this book.  
====> ☆☆☆  __["Writing An Interpreter in Go"](https://interpreterbook.com/)__  ☆☆☆  
====> ☆☆☆  __["Writing A Compiler In Go"](https://compilerbook.com/)__  ☆☆☆  
That interpreter and compiler-VM is called Monkey in the book.  
The Monkey is written in Go in the book.  
But in this repository it is written in Rust.  

## Supports

- [x] Lexer
- [x] Parser
- [x] Evaluator
- [x] Compiler
- [x] VM
- [x] REPL
- [x] Test case
- [x] Evaluator and VM benchmarks
- [x] Not use `unsafe`

## Example

### REPL

```sh
$ cargo run
>> let a = 5
5
>> a + 10
15
>> let new_closure = fn(a) { fn() { a; }; };
Closure[CompiledFunction[0000 GetLocal 0¥n0002 Closure 3 1¥n0006 ReturnValue¥n] ]
>> let closure = new_closure(99);
Closure[CompiledFunction[0000 GetFree 0¥n0002 ReturnValue¥n] 99]
>> closure();
99
```

### Fibonacchi

```monkey
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
fibonacci(15); #=> 610
```

## TODO

- [ ] Improve print output
- [ ] Improve REPL
- [ ] Refactoring
- [ ] Optimize data structure
- [ ] Support LLVM

## Contributors

- [ktanaka101](https://github.com/ktanaka101) - creator, maintainer

## License

MIT
