use std::cell::RefCell;
use std::rc::Rc;

use crate::parser::ast;

use super::super::env;
use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub params: Vec<ast::Identifier>,
    pub body: ast::Block,
    pub env: Rc<RefCell<env::Environment>>,
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "fn({}) {}",
            self.params
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<String>>()
                .join(""),
            self.body
        )
    }
}
