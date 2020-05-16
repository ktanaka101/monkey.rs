use std::fmt;
use std::fmt::{Display, Formatter};

use crate::builtin;

use super::{Error, Object};

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
