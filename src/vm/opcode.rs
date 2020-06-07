mod constant;

pub use constant::Constant;

use crate::compiler::convert::ToBytes;

use vm::convert::TryRead;

mod preludes {
    pub use super::super::preludes::*;
    pub use crate::vm::bytecode::{Instruction, Instructions};
}

use preludes::*;

#[derive(Debug)]
pub enum Opcode {
    Constant(Constant),
}

impl Opcode {
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Opcode::Constant(o) => o.to_bytes().to_vec(),
        }
    }
}

impl From<Constant> for Opcode {
    fn from(value: Constant) -> Self {
        Opcode::Constant(value)
    }
}

impl TryFrom<&[Instruction]> for Opcode {
    type Error = anyhow::Error;

    fn try_from(value: &[Instruction]) -> Result<Self> {
        match value[0] {
            Constant::CODE => Ok(Constant(Constant::try_read(&value[1..])?).into()),
            bad_code => Err(anyhow::format_err!("Unsupported code {}", bad_code)),
        }
    }
}

pub trait OperandCode {
    const CODE: u8;
    fn code() -> u8 {
        Self::CODE
    }
    fn name() -> &'static str;
}
