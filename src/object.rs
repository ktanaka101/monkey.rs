mod prelude {
    pub use std::fmt;
    pub use std::fmt::{Display, Formatter};
}
use prelude::*;

mod array;
mod boolean;
mod error;
mod function;
mod hashable;
mod integer;
mod mbuiltin;
mod mhash;
mod mreturn;
mod null;
mod string_lit;

pub use array::Array;
pub use boolean::Boolean;
pub use error::Error;
pub use function::Function;
pub use hashable::HashableObject;
pub use integer::Integer;
pub use mbuiltin::Builtin;
pub use mhash::{Hash, HashPairs};
pub use mreturn::Return;
pub use null::Null;
pub use string_lit::StringLit;

#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Integer(Integer),
    Boolean(Boolean),
    Error(Error),
    Return(Return),
    Function(Function),
    StringLit(StringLit),
    Builtin(Builtin),
    Array(Array),
    Hash(Hash),
    Null(Null),
}

impl From<Integer> for Object {
    fn from(obj: Integer) -> Object {
        Object::Integer(obj)
    }
}
impl From<Boolean> for Object {
    fn from(obj: Boolean) -> Object {
        Object::Boolean(obj)
    }
}
impl From<Error> for Object {
    fn from(obj: Error) -> Object {
        Object::Error(obj)
    }
}
impl From<Return> for Object {
    fn from(obj: Return) -> Object {
        Object::Return(obj)
    }
}
impl From<Function> for Object {
    fn from(obj: Function) -> Object {
        Object::Function(obj)
    }
}
impl From<StringLit> for Object {
    fn from(obj: StringLit) -> Object {
        Object::StringLit(obj)
    }
}
impl From<Builtin> for Object {
    fn from(obj: Builtin) -> Object {
        Object::Builtin(obj)
    }
}
impl From<Array> for Object {
    fn from(obj: Array) -> Object {
        Object::Array(obj)
    }
}
impl From<Hash> for Object {
    fn from(obj: Hash) -> Object {
        Object::Hash(obj)
    }
}
impl From<Null> for Object {
    fn from(obj: Null) -> Object {
        Object::Null(obj)
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(o) => write!(f, "{}", o),
            Self::Boolean(o) => write!(f, "{}", o),
            Self::Error(o) => write!(f, "{}", o),
            Self::Return(o) => write!(f, "{}", o),
            Self::Function(o) => write!(f, "{}", o),
            Self::StringLit(o) => write!(f, "{}", o),
            Self::Builtin(o) => write!(f, "{}", o),
            Self::Array(o) => write!(f, "{}", o),
            Self::Hash(o) => write!(f, "{}", o),
            Self::Null(o) => write!(f, "{}", o),
        }
    }
}
impl Object {
    pub fn o_type(&self) -> &'static str {
        match self {
            Self::Integer(_) => "Integer",
            Self::Boolean(_) => "Boolean",
            Self::Error(_) => "Error",
            Self::Return(_) => "Return",
            Self::Function(_) => "Function",
            Self::StringLit(_) => "StringLit",
            Self::Builtin(_) => "Builtin",
            Self::Array(_) => "Array",
            Self::Hash(_) => "Hash",
            Self::Null(_) => "Null",
        }
    }

    pub fn try_into_hashable_object(self) -> Option<HashableObject> {
        Some(match self {
            Self::Integer(i) => HashableObject::Integer(i),
            Self::Boolean(b) => HashableObject::Boolean(b),
            Self::StringLit(s) => HashableObject::StringLit(s),
            _ => return None,
        })
    }
}
