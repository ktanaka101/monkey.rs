use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: Expr,
}

impl Display for ExprStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expr)
    }
}

impl TryFrom<Stmt> for ExprStmt {
    type Error = Error;

    fn try_from(value: Stmt) -> Result<Self> {
        match value {
            Stmt::ExprStmt(expr_stmt) => Ok(expr_stmt),
            stmt => Err(ParserError::Convert(
                format!("{:?}", stmt),
                "ExprStmt".into(),
            ))?,
        }
    }
}
