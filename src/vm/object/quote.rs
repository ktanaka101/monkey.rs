use crate::parser::ast::Node;

use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Quote {
    pub node: Node,
}

impl Display for Quote {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.node)
    }
}
