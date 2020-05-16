use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Identifier(Identifier),
    PrefixExpr(PrefixExpr),
    InfixExpr(InfixExpr),
    If(If),
    Function(Function),
    Call(Call),
    Integer(Integer),
    Boolean(Boolean),
    StringLit(StringLit),
    Array(Array),
    Index(Index),
    Hash(Hash),
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}
