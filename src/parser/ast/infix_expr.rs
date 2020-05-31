use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct InfixExpr {
    pub left: Box<Expr>,
    pub ope: Operator,
    pub right: Box<Expr>,
}

impl Display for InfixExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.ope, self.right)
    }
}

impl TryFrom<Expr> for InfixExpr {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::InfixExpr(infix_expr) => Ok(infix_expr),
            expr => Err(ParserError::Convert(
                format!("{:?}", expr),
                "InfixExpr".into(),
            ))?,
        }
    }
}
