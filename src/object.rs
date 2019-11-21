use crate::ast;
use crate::builtin;
use crate::env;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::hash;
use std::rc::Rc;

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
    pub fn o_type(&self) -> String {
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
        .to_string()
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

#[derive(Debug, Clone, Eq)]
pub struct Boolean {
    pub value: bool,
}
impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
impl hash::Hash for Boolean {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}
impl PartialEq for Boolean {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub struct Null();
impl Display for Null {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "null")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub value: Box<Object>,
}
impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    pub message: String,
}
impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "ERROR: {}", self.message)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub params: Vec<ast::Identifier>,
    pub body: ast::Block,
    pub env: Rc<RefCell<env::Environment>>,
}
impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "fn({}) {{\n{}\n}}",
            self.params
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<String>>()
                .join(""),
            self.body
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Builtin {
    pub func: builtin::BuiltinFunction,
}
impl Display for Builtin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "builtin function.")
    }
}
impl Builtin {
    pub fn call(&self, args: &[Object]) -> Result<Object, Error> {
        self.func.call(args)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Array {
    pub elements: Vec<Object>,
}
impl Display for Array {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .elements
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<String>>()
            .join(", ");

        write!(f, "{}", out)
    }
}

pub type HashPairs = HashMap<HashableObject, Object>;

#[derive(Debug, Clone, PartialEq)]
pub struct Hash {
    pub pairs: HashPairs,
}
impl Display for Hash {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .pairs
            .iter()
            .map(|(k, v)| format!("{}, {}", k, v))
            .collect::<Vec<String>>()
            .join("");

        write!(f, "{}", out)
    }
}
