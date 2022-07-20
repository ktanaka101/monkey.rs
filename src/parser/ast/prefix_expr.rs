use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct PrefixExpr {
    pub ope: Operator,
    pub right: Box<Expr>,
}

impl Display for PrefixExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.ope, self.right.as_ref())
    }
}

impl TryFrom<Expr> for PrefixExpr {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::PrefixExpr(prefix_expr) => Ok(prefix_expr),
            expr => Err(ParserError::Convert(format!("{:?}", expr), "PrefixExpr".into()).into()),
        }
    }
}
