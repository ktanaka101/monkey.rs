use std::hash;

use super::prelude::*;

#[derive(Debug, Clone, Eq)]
pub struct StringLit {
    pub value: String,
}
impl Display for StringLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
impl hash::Hash for StringLit {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}
impl PartialEq for StringLit {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}
