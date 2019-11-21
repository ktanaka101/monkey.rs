use std::fmt;
use std::result;

#[derive(Debug)]
pub enum MonkeyError {
  Parser(String),
}

impl fmt::Display for MonkeyError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      MonkeyError::Parser(err) => write!(f, "Parser error: {}", err),
    }
  }
}

pub type Result<T> = result::Result<T, MonkeyError>;
