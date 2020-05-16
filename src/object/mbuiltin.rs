use crate::builtin;

use super::prelude::*;
use super::{Error, Object};

#[derive(Debug, Clone, PartialEq)]
pub struct Builtin {
    pub func: builtin::Function,
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
