use super::prelude::*;
use super::{
    Array, Boolean, Builtin, Error, Function, Hash, Integer, Null, Quote, Return, StringLit,
};

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
    Quote(Quote),
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
impl From<Quote> for Object {
    fn from(obj: Quote) -> Object {
        Object::Quote(obj)
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
            Self::Quote(o) => write!(f, "{}", o),
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
            Self::Quote(_) => "Quote",
        }
    }
}
