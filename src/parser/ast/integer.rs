use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Integer {
    pub value: i64,
}

impl Display for Integer {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl TryFrom<Expr> for Integer {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Integer(int) => Ok(int),
            expr => {
                return Err(ParserError::Convert(format!("{:?}", expr), "Integer".into()).into())
            }
        }
    }
}
