mod inst;

pub use inst::{Instruction, Instructions};

use crate::evaluator::objects;

mod preludes {
    pub use super::super::preludes::*;
}

#[derive(Debug, Default, Clone)]
pub struct Bytecode {
    pub instructions: inst::Instructions,
    pub constants: Vec<objects::Object>,
}
