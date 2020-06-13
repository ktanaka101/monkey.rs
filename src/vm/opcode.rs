mod add;
mod constant;
mod pop;

pub use add::Add;
pub use constant::Constant;
pub use pop::Pop;

use crate::compiler::convert::ToBytes;

use vm::convert::{Read, TryRead};

mod preludes {
    pub use super::super::preludes::*;
    pub use crate::vm::bytecode::{Instruction, Instructions};
    pub use crate::vm::opcode::{OperandCode, OperandType};
}

use preludes::*;

pub enum OperandType {
    Constant = 0,
    Add = 1,
    Pop = 2,
}

impl TryFrom<u8> for OperandType {
    type Error = anyhow::Error;

    fn try_from(value: u8) -> Result<Self> {
        Ok(match value {
            0 => Self::Constant,
            1 => Self::Add,
            2 => Self::Pop,
            bad => Err(anyhow::format_err!("Unsupported id {}", bad))?,
        })
    }
}

impl From<OperandType> for u8 {
    fn from(value: OperandType) -> Self {
        value as u8
    }
}

#[derive(Debug)]
pub enum Opcode {
    Constant(Constant),
    Add(Add),
    Pop(Pop),
}

impl Opcode {
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Opcode::Constant(o) => o.to_bytes().to_vec(),
            Opcode::Add(o) => o.to_bytes().to_vec(),
            Opcode::Pop(o) => o.to_bytes().to_vec(),
        }
    }

    pub fn readsize(&self) -> usize {
        match self {
            Opcode::Constant(o) => o.readsize(),
            Opcode::Add(o) => o.readsize(),
            Opcode::Pop(o) => o.readsize(),
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

impl From<Pop> for Opcode {
    fn from(value: Pop) -> Self {
        Opcode::Pop(value)
    }
}

impl TryFrom<&[Instruction]> for Opcode {
    type Error = anyhow::Error;

    fn try_from(value: &[Instruction]) -> Result<Self> {
        let ope_type = OperandType::try_from(value[0])?;
        match ope_type {
            OperandType::Constant => Ok(Constant(Constant::try_read(&value[1..])?).into()),
            OperandType::Add => Ok(Add.into()),
            OperandType::Pop => Ok(Pop.into()),
        }
    }
}

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(o) => write!(f, "{}", o),
            Self::Add(o) => write!(f, "{}", o),
            Self::Pop(o) => write!(f, "{}", o),
        }
    }
}

pub trait OperandCode {
    const TYPE: OperandType;
    fn ope_type(&self) -> OperandType {
        Self::TYPE
    }
    const NAME: &'static str;
    fn name(&self) -> &'static str {
        Self::NAME
    }
}
