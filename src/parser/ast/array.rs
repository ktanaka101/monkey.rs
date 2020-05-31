use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Array {
    pub elements: Vec<Expr>,
}

impl Display for Array {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .elements
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<String>>()
            .join(", ");

        write!(f, "[{}]", out)
    }
}

impl TryFrom<Expr> for Array {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Array(arr) => Ok(arr),
            expr => Err(ParserError::Convert(format!("{:?}", expr), "Array".into()))?,
        }
    }
}
