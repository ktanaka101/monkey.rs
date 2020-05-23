use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct PrefixExpr {
    pub token: Token,
    pub ope: Operator,
    pub right: Box<Expr>,
}

impl Display for PrefixExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.ope, self.right.as_ref())
    }
}
