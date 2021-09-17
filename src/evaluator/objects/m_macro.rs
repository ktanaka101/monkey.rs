use std::cell::RefCell;
use std::rc::Rc;

use crate::parser::ast;

use super::super::env;
use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    pub params: Vec<ast::Identifier>,
    pub body: ast::Block,
    pub env: Rc<RefCell<env::Environment>>,
}

impl Macro {
    const fn literal(&self) -> &'static str {
        "macro"
    }
}

impl Display for Macro {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({}) {{\n{}\n}}",
            self.literal(),
            self.params
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<String>>()
                .join(""),
            self.body
        )
    }
}
