use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    pub value: String,
}

impl Display for Identifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl TryFrom<Expr> for Identifier {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Identifier(ident) => Ok(ident),
            expr => Err(ParserError::Convert(
                format!("{:?}", expr),
                "Identifier".into(),
            ))?,
        }
    }
}
