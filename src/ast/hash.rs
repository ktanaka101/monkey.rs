use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Hash {
    pub token: Token,
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
