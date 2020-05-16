use std::hash;

use super::prelude::*;
use super::{Boolean, Integer, StringLit};

#[derive(Debug, Clone, Eq)]
pub enum HashableObject {
    Integer(Integer),
    Boolean(Boolean),
    StringLit(StringLit),
}
impl Display for HashableObject {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self)
    }
}
impl hash::Hash for HashableObject {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Integer(x) => x.hash(state),
            Self::Boolean(x) => x.hash(state),
            Self::StringLit(x) => x.hash(state),
        };
    }
}
impl PartialEq for HashableObject {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(x), Self::Integer(y)) => x.eq(y),
            (Self::Boolean(x), Self::Boolean(y)) => x.eq(y),
            (Self::StringLit(x), Self::StringLit(y)) => x.eq(y),
            (_, _) => false,
        }
    }
}
