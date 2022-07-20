use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Index {
    pub left: Box<Expr>,
    pub index: Box<Expr>,
}

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}

impl TryFrom<Expr> for Index {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Index(idx) => Ok(idx),
            expr => Err(ParserError::Convert(format!("{:?}", expr), "Index".into()).into()),
        }
    }
}
