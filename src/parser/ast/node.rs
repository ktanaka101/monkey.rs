use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Program(Program),
    Stmt(Stmt),
    Expr(Expr),
}

impl Display for Node {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Program(n) => write!(f, "{}", n),
            Self::Stmt(n) => write!(f, "{}", n),
            Self::Expr(n) => write!(f, "{}", n),
        }
    }
}

impl From<Program> for Node {
    fn from(node: Program) -> Self {
        Node::Program(node)
    }
}

impl From<Stmt> for Node {
    fn from(node: Stmt) -> Self {
        Node::Stmt(node)
    }
}

impl From<Expr> for Node {
    fn from(node: Expr) -> Self {
        Node::Expr(node)
    }
}
