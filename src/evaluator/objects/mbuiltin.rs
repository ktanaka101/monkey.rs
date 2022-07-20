use anyhow::Result;

use super::super::builtin;
use super::prelude::*;
use super::Object;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Builtin {
    pub func: builtin::Function,
}

impl Display for Builtin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "builtin function.")
    }
}

impl Builtin {
    pub fn call(&self, args: &[Object]) -> Result<Option<Object>> {
        self.func.call(args)
    }
}
