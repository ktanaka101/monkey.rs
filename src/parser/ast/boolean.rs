use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Boolean {
    pub token: Token,
    pub value: bool,
}

impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal())
    }
}
