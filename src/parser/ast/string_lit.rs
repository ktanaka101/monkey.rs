use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct StringLit {
    pub value: String,
}

impl Display for StringLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl TryFrom<Expr> for StringLit {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::StringLit(string) => Ok(string),
            expr => Err(ParserError::Convert(
                format!("{:?}", expr),
                "StringLit".into(),
            ))?,
        }
    }
}
