mod add;
mod constant;
mod div;
mod equal;
mod greater_than;
mod mul;
mod not_equal;
mod ofalse;
mod otrue;
mod pop;
mod sub;

pub use add::Add;
pub use constant::Constant;
pub use div::Div;
pub use equal::Equal;
pub use greater_than::GreaterThan;
pub use mul::Mul;
pub use not_equal::NotEqual;
pub use ofalse::False;
pub use otrue::True;
pub use pop::Pop;
pub use sub::Sub;

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
    Sub = 3,
    Mul = 4,
    Div = 5,
    True = 6,
    False = 7,
    Equal = 8,
    NotEqual = 9,
    GreaterThan = 10,
}

impl TryFrom<u8> for OperandType {
    type Error = anyhow::Error;

    fn try_from(value: u8) -> Result<Self> {
        Ok(match value {
            0 => Self::Constant,
            1 => Self::Add,
            2 => Self::Pop,
            3 => Self::Sub,
            4 => Self::Mul,
            5 => Self::Div,
            6 => Self::True,
            7 => Self::False,
            8 => Self::Equal,
            9 => Self::NotEqual,
            10 => Self::GreaterThan,
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
    Sub(Sub),
    Mul(Mul),
    Div(Div),
    True(True),
    False(False),
    Equal(Equal),
    NotEqual(NotEqual),
    GreaterThan(GreaterThan),
}

impl Opcode {
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Opcode::Constant(o) => o.to_bytes().to_vec(),
            Opcode::Add(o) => o.to_bytes().to_vec(),
            Opcode::Pop(o) => o.to_bytes().to_vec(),
            Opcode::Sub(o) => o.to_bytes().to_vec(),
            Opcode::Mul(o) => o.to_bytes().to_vec(),
            Opcode::Div(o) => o.to_bytes().to_vec(),
            Opcode::True(o) => o.to_bytes().to_vec(),
            Opcode::False(o) => o.to_bytes().to_vec(),
            Opcode::Equal(o) => o.to_bytes().to_vec(),
            Opcode::NotEqual(o) => o.to_bytes().to_vec(),
            Opcode::GreaterThan(o) => o.to_bytes().to_vec(),
        }
    }

    pub fn readsize(&self) -> usize {
        match self {
            Opcode::Constant(o) => o.readsize(),
            Opcode::Add(o) => o.readsize(),
            Opcode::Pop(o) => o.readsize(),
            Opcode::Sub(o) => o.readsize(),
            Opcode::Mul(o) => o.readsize(),
            Opcode::Div(o) => o.readsize(),
            Opcode::True(o) => o.readsize(),
            Opcode::False(o) => o.readsize(),
            Opcode::Equal(o) => o.readsize(),
            Opcode::NotEqual(o) => o.readsize(),
            Opcode::GreaterThan(o) => o.readsize(),
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

impl From<Sub> for Opcode {
    fn from(value: Sub) -> Self {
        Opcode::Sub(value)
    }
}

impl From<Mul> for Opcode {
    fn from(value: Mul) -> Self {
        Opcode::Mul(value)
    }
}

impl From<Div> for Opcode {
    fn from(value: Div) -> Self {
        Opcode::Div(value)
    }
}

impl From<True> for Opcode {
    fn from(value: True) -> Self {
        Opcode::True(value)
    }
}

impl From<False> for Opcode {
    fn from(value: False) -> Self {
        Opcode::False(value)
    }
}

impl From<Equal> for Opcode {
    fn from(value: Equal) -> Self {
        Opcode::Equal(value)
    }
}

impl From<NotEqual> for Opcode {
    fn from(value: NotEqual) -> Self {
        Opcode::NotEqual(value)
    }
}

impl From<GreaterThan> for Opcode {
    fn from(value: GreaterThan) -> Self {
        Opcode::GreaterThan(value)
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
            OperandType::Sub => Ok(Sub.into()),
            OperandType::Mul => Ok(Mul.into()),
            OperandType::Div => Ok(Div.into()),
            OperandType::True => Ok(True.into()),
            OperandType::False => Ok(False.into()),
            OperandType::Equal => Ok(Equal.into()),
            OperandType::NotEqual => Ok(NotEqual.into()),
            OperandType::GreaterThan => Ok(GreaterThan.into()),
        }
    }
}

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(o) => write!(f, "{}", o),
            Self::Add(o) => write!(f, "{}", o),
            Self::Pop(o) => write!(f, "{}", o),
            Self::Sub(o) => write!(f, "{}", o),
            Self::Mul(o) => write!(f, "{}", o),
            Self::Div(o) => write!(f, "{}", o),
            Self::True(o) => write!(f, "{}", o),
            Self::False(o) => write!(f, "{}", o),
            Self::Equal(o) => write!(f, "{}", o),
            Self::NotEqual(o) => write!(f, "{}", o),
            Self::GreaterThan(o) => write!(f, "{}", o),
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
