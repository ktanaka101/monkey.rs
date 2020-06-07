mod add;
mod constant;

pub use add::Add;
pub use constant::Constant;

use crate::compiler::convert::ToBytes;

use vm::convert::{Read, TryRead};

mod preludes {
    pub use super::super::preludes::*;
    pub use crate::vm::bytecode::{Instruction, Instructions};
    pub use crate::vm::opcode::OperandCode;
}

use preludes::*;

#[derive(Debug)]
pub enum Opcode {
    Constant(Constant),
    Add(Add),
}

impl Opcode {
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Opcode::Constant(o) => o.to_bytes().to_vec(),
            Opcode::Add(o) => o.to_bytes().to_vec(),
        }
    }

    pub fn readsize(&self) -> usize {
        match self {
            Opcode::Constant(o) => o.readsize(),
            Opcode::Add(o) => o.readsize(),
        }
    }
}

impl From<Constant> for Opcode {
    fn from(value: Constant) -> Self {
        Opcode::Constant(value)
    }
}

impl From<Add> for Opcode {
    fn from(value: Add) -> Self {
        Opcode::Add(value)
    }
}

impl TryFrom<&[Instruction]> for Opcode {
    type Error = anyhow::Error;

    fn try_from(value: &[Instruction]) -> Result<Self> {
        match value[0] {
            Constant::CODE => Ok(Constant(Constant::try_read(&value[1..])?).into()),
            Add::CODE => Ok(Add.into()),
            bad_code => Err(anyhow::format_err!("Unsupported code {}", bad_code)),
        }
    }
}

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(o) => write!(f, "{}", o),
            Self::Add(o) => write!(f, "{}", o),
        }
    }
}

pub trait OperandCode {
    const CODE: u8;
    fn code(&self) -> u8 {
        Self::CODE
    }
    const NAME: &'static str;
    fn name(&self) -> &'static str {
        Self::NAME
    }
}
