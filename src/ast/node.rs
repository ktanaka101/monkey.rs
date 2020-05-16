use super::prelude::*;

#[derive(Debug, PartialEq)]
pub enum Node {
    Program(Program),
    Stmt(Stmt),
    Expr(Expr),
}

impl Display for Node {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl From<Program> for Node {
    fn from(node: Program) -> Self {
        Node::Program(node)
    }
}
