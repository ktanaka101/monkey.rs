use crate::vm::bytecode;

use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct CompiledFunction {
    pub instructions: bytecode::Instructions,
}

impl Display for CompiledFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CompiledFunction[{}]", self.instructions)
    }
}
