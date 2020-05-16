use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Integer {
    pub token: Token,
    pub value: i64,
}

impl Display for Integer {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}
