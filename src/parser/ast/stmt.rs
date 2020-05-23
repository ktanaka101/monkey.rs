use super::prelude::*;
use super::{Block, ExprStmt, Let, Return};

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmt(ExprStmt),
    Let(Let),
    Return(Return),
    Block(Block),
}

impl From<Block> for Stmt {
    fn from(stmt: Block) -> Self {
        Stmt::Block(stmt)
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExprStmt(s) => write!(f, "{}", s),
            Self::Let(s) => write!(f, "{}", s),
            Self::Block(s) => write!(f, "{}", s),
            Self::Return(s) => write!(f, "{}", s),
        }
    }
}
