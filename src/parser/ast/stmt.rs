use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmt(ExprStmt),
    Let(Let),
    Return(Return),
    Block(Block),
}

impl From<ExprStmt> for Stmt {
    fn from(stmt: ExprStmt) -> Self {
        Stmt::ExprStmt(stmt)
    }
}

impl From<Let> for Stmt {
    fn from(stmt: Let) -> Self {
        Stmt::Let(stmt)
    }
}

impl From<Return> for Stmt {
    fn from(stmt: Return) -> Self {
        Stmt::Return(stmt)
    }
}

impl From<Block> for Stmt {
    fn from(stmt: Block) -> Self {
        Stmt::Block(stmt)
    }
}

impl TryFrom<Node> for Stmt {
    type Error = Error;
    fn try_from(value: Node) -> Result<Self> {
        match value {
            Node::Stmt(stmt) => Ok(stmt),
            Node::Program(program) => Err(ParserError::Convert(
                format!("{:?}", program),
                "Stmt".into(),
            ))?,
            Node::Expr(expr) => Ok(Stmt::ExprStmt(ExprStmt { expr })),
        }
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
