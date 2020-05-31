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