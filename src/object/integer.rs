use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash;

#[derive(Debug, Clone, Eq)]
pub struct Integer {
    pub value: i64,
}
impl Display for Integer {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
impl hash::Hash for Integer {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}
impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}
