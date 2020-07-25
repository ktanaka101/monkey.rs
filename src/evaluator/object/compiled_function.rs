use crate::vm::bytecode;

use super::prelude::*;

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CompiledFunction {
    pub instructions: bytecode::Instructions,
    pub num_locals: u16,
    pub num_parameters: u8,
}

impl Display for CompiledFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CompiledFunction[{}]", self.instructions)
    }
}
