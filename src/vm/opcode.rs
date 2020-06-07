mod constant;

pub use constant::OpConstant;

use crate::compiler::convert::ToBytes;

use vm::convert::TryRead;

mod preludes {
    pub use super::super::preludes::*;
    pub use crate::vm::bytecode::{Instruction, Instructions};
}

use preludes::*;

#[derive(Debug)]
pub enum Opcode {
    OpConstant(OpConstant),
}

impl Opcode {
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Opcode::OpConstant(o) => o.to_bytes().to_vec(),
        }
    }
}

impl From<OpConstant> for Opcode {
    fn from(value: OpConstant) -> Self {
        Opcode::OpConstant(value)
    }
}

impl TryFrom<&[Instruction]> for Opcode {
    type Error = anyhow::Error;

    fn try_from(value: &[Instruction]) -> Result<Self> {
        match value[0] {
            OpConstant::CODE => Ok(OpConstant(OpConstant::try_read(&value[1..])?).into()),
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
