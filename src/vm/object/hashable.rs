use std::convert::TryFrom;
use std::hash;

use super::prelude::*;
use super::{Boolean, Integer, Object, StringLit};

#[derive(Debug, Clone, Eq)]
pub enum HashableObject {
    Integer(Integer),
    Boolean(Boolean),
    StringLit(StringLit),
}

impl Display for HashableObject {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HashableObject::Integer(o) => write!(f, "{}", o),
            HashableObject::Boolean(o) => write!(f, "{}", o),
            HashableObject::StringLit(o) => write!(f, "{}", o),
        }        
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

impl TryFrom<Object> for HashableObject {
    type Error = String;
    fn try_from(value: Object) -> Result<HashableObject, String> {
        Ok(match value {
            Object::Integer(i) => HashableObject::Integer(i),
            Object::Boolean(b) => HashableObject::Boolean(b),
            Object::StringLit(s) => HashableObject::StringLit(s),
            _ => return Err(format!("Unsupported object.({:?})", value)),
        })
    }
}
