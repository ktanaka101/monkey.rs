use crate::vm::bytecode;

use super::prelude::*;

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CompiledFunction {
    pub instructions: bytecode::Instructions,
}

impl Display for CompiledFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CompiledFunction[{}]", self.instructions)
    }
}