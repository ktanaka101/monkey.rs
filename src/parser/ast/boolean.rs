use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Boolean {
    pub value: bool,
}

impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl TryFrom<Expr> for Boolean {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Boolean(b) => Ok(b),
            expr => Err(ParserError::Convert(
                format!("{:?}", expr),
                "Boolean".into(),
            ))?,
        }
    }
}
