use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Hash {
    pub pairs: Vec<Pair>,
}

impl Display for Hash {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .pairs
            .iter()
            .map(|pair| format!("{}:{}", pair.key, pair.value))
            .collect::<Vec<String>>()
            .join(", ");

        write!(f, "{}", out)
    }
}

impl TryFrom<Expr> for Hash {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Hash(hs) => Ok(hs),
            expr => return Err(ParserError::Convert(format!("{:?}", expr), "Hash".into()).into()),
        }
    }
}
