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
        match self {
            Self::Identifier(e) => write!(f, "{}", e),
            Self::PrefixExpr(e) => write!(f, "{}", e),
            Self::InfixExpr(e) => write!(f, "{}", e),
            Self::If(e) => write!(f, "{}", e),
            Self::Function(e) => write!(f, "{}", e),
            Self::Call(e) => write!(f, "{}", e),
            Self::Integer(e) => write!(f, "{}", e),
            Self::Boolean(e) => write!(f, "{}", e),
            Self::StringLit(e) => write!(f, "{}", e),
            Self::Array(e) => write!(f, "{}", e),
            Self::Index(e) => write!(f, "{}", e),
            Self::Hash(e) => write!(f, "{}", e),
        }
    }
}
