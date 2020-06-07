#![feature(const_generics)]

mod preludes {
    pub use anyhow::Result;
    pub use std::convert::{TryFrom, TryInto};
    pub use std::fmt;
    pub use std::fmt::{Display, Formatter};
}

mod compiler;
mod lexer;
mod parser;

pub mod evaluator;
pub mod repl;
pub mod vm;
