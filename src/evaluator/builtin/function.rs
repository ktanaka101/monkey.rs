use std::convert::TryFrom;

use anyhow::Result;

use crate::evaluator::new_error;
use crate::evaluator::object;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Function {
    Len,
    First,
    Last,
    Rest,
    Push,
    Puts,
}

static FUNCTIONS: [Function; 6] = [
    Function::Len,
    Function::First,
    Function::Last,
    Function::Rest,
    Function::Push,
    Function::Puts,
];

impl Function {
    pub fn iterator() -> std::slice::Iter<'static, Function> {
        FUNCTIONS.iter()
    }

    pub fn by_index(idx: usize) -> Function {
        FUNCTIONS[idx].clone()
    }

    pub fn name(&self) -> &'static str {
        match *self {
            Function::Len => "len",
            Function::First => "first",
            Function::Last => "last",
            Function::Rest => "rest",
            Function::Push => "push",
            Function::Puts => "puts",
        }
    }
}

impl TryFrom<&str> for Function {
    type Error = &'static str;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "len" => Ok(Self::Len),
            "first" => Ok(Self::First),
            "last" => Ok(Self::Last),
            "rest" => Ok(Self::Rest),
            "push" => Ok(Self::Push),
            "puts" => Ok(Self::Puts),
            _ => Err("Not found builtin function."),
        }
    }
}

impl From<Function> for object::Object {
    fn from(value: Function) -> Self {
        object::Builtin { func: value }.into()
    }
}

impl Function {
    pub fn call(&self, args: &[object::Object]) -> Result<Option<object::Object>> {
        match self {
            Self::Len => len(args),
            Self::First => first(args),
            Self::Last => last(args),
            Self::Rest => rest(args),
            Self::Push => push(args),
            Self::Puts => puts(args),
        }
    }
}

fn len(args: &[object::Object]) -> Result<Option<object::Object>> {
    if args.len() != 1 {
        return new_error(&format!(
            "wrong number of arguments. got={}, want=1",
            args.len()
        ));
    }

    let count = match &args[0] {
        object::Object::StringLit(arg) => arg.value.chars().count(),
        object::Object::Array(arg) => arg.elements.len(),
        arg => {
            return new_error(&format!(
                "argument to 'len' not supported, got {}",
                arg.o_type()
            ));
        }
    };

    Ok(Some(
        object::Integer {
            value: i64::try_from(count).or_else(|e| new_error(&e.to_string()))?,
        }
        .into(),
    ))
}

fn first(args: &[object::Object]) -> Result<Option<object::Object>> {
    if args.len() != 1 {
        return new_error(&format!(
            "wrong number of arguments. got={}, want=1",
            args.len()
        ));
    }

    match &args[0] {
        object::Object::Array(arr) => {
            let res = arr.elements.first();
            Ok(res.map(|o| o.clone()))
        }
        not_arr => new_error(&format!(
            "argument to 'first' must be Array, got {}",
            not_arr.o_type()
        )),
    }
}

fn last(args: &[object::Object]) -> Result<Option<object::Object>> {
    if args.len() != 1 {
        return new_error(&format!(
            "wrong number of arguments. got={}, want=1",
            args.len()
        ));
    }

    match &args[0] {
        object::Object::Array(arr) => {
            let res = arr.elements.last();
            Ok(res.map(|o| o.clone()))
        }
        not_arr => new_error(&format!(
            "argument to 'last' must be Array, got {}",
            not_arr.o_type()
        )),
    }
}

fn rest(args: &[object::Object]) -> Result<Option<object::Object>> {
    if args.len() != 1 {
        return new_error(&format!(
            "wrong number of arguments. got={}, want=1",
            args.len()
        ));
    }

    match &args[0] {
        object::Object::Array(arr) => {
            if arr.elements.is_empty() {
                return Ok(None);
            }

            Ok(Some(
                object::Array {
                    elements: arr.elements[1..].to_vec(),
                }
                .into(),
            ))
        }
        not_arr => new_error(&format!(
            "argument to 'rest' must be Array, got {}",
            not_arr.o_type()
        )),
    }
}

fn push(args: &[object::Object]) -> Result<Option<object::Object>> {
    if args.len() != 2 {
        return new_error(&format!(
            "wrong number of arguments. got={}, want=2",
            args.len()
        ));
    }

    match &args[0] {
        object::Object::Array(ref arr) => {
            let mut v = arr.elements.clone();
            v.push(args[1].clone());

            Ok(Some(object::Array { elements: v }.into()))
        }
        not_arr => new_error(&format!(
            "argument to 'push' must be Array, got {}",
            not_arr.o_type()
        )),
    }
}

fn puts(args: &[object::Object]) -> Result<Option<object::Object>> {
    for arg in args.iter() {
        println!("{}", arg);
    }
    Ok(None)
}
