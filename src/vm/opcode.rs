mod add;
mod array;
mod bang;
mod call;
mod closure;
mod constant;
mod current_closure;
mod div;
mod equal;
mod get_builtin;
mod get_free;
mod get_global;
mod get_local;
mod greater_than;
mod hash;
mod index;
mod jump;
mod jump_not_truthy;
mod minus;
mod mreturn;
mod mul;
mod not_equal;
mod null;
mod ofalse;
mod otrue;
mod pop;
mod return_value;
mod set_global;
mod set_local;
mod sub;

pub use add::Add;
pub use array::Array;
pub use bang::Bang;
pub use call::Call;
pub use closure::Closure;
pub use constant::Constant;
pub use current_closure::CurrentClosure;
pub use div::Div;
pub use equal::Equal;
pub use get_builtin::GetBuiltin;
pub use get_free::GetFree;
pub use get_global::GetGlobal;
pub use get_local::GetLocal;
pub use greater_than::GreaterThan;
pub use hash::Hash;
pub use index::Index;
pub use jump::Jump;
pub use jump_not_truthy::JumpNotTruthy;
pub use minus::Minus;
pub use mreturn::Return;
pub use mul::Mul;
pub use not_equal::NotEqual;
pub use null::Null;
pub use ofalse::False;
pub use otrue::True;
pub use pop::Pop;
pub use return_value::ReturnValue;
pub use set_global::SetGlobal;
pub use set_local::SetLocal;
pub use sub::Sub;

use crate::vm::convert::ToBytes;

use vm::convert::{Read, TryRead};

mod preludes {
    pub use super::super::preludes::*;
    pub use crate::vm::bytecode::Instruction;
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
    Minus = 11,
    Bang = 12,
    JumpNotTruthy = 13,
    Jump = 14,
    Null = 15,
    GetGlobal = 16,
    SetGlobal = 17,
    Array = 18,
    Hash = 19,
    Index = 20,
    Call = 21,
    ReturnValue = 22,
    Return = 23,
    GetLocal = 24,
    SetLocal = 25,
    GetBuiltin = 26,
    Closure = 27,
    GetFree = 28,
    CurrentClosure = 29,
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
            11 => Self::Minus,
            12 => Self::Bang,
            13 => Self::JumpNotTruthy,
            14 => Self::Jump,
            15 => Self::Null,
            16 => Self::GetGlobal,
            17 => Self::SetGlobal,
            18 => Self::Array,
            19 => Self::Hash,
            20 => Self::Index,
            21 => Self::Call,
            22 => Self::ReturnValue,
            23 => Self::Return,
            24 => Self::GetLocal,
            25 => Self::SetLocal,
            26 => Self::GetBuiltin,
            27 => Self::Closure,
            28 => Self::GetFree,
            29 => Self::CurrentClosure,
            bad => return Err(anyhow::format_err!("Unsupported id {}", bad)),
        })
    }
}

impl From<OperandType> for u8 {
    fn from(value: OperandType) -> Self {
        value as u8
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
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
    Minus(Minus),
    Bang(Bang),
    JumpNotTruthy(JumpNotTruthy),
    Jump(Jump),
    Null(Null),
    GetGlobal(GetGlobal),
    SetGlobal(SetGlobal),
    Array(Array),
    Hash(Hash),
    Index(Index),
    Call(Call),
    ReturnValue(ReturnValue),
    Return(Return),
    GetLocal(GetLocal),
    SetLocal(SetLocal),
    GetBuiltin(GetBuiltin),
    Closure(Closure),
    GetFree(GetFree),
    CurrentClosure(CurrentClosure),
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
            Opcode::Minus(o) => o.to_bytes().to_vec(),
            Opcode::Bang(o) => o.to_bytes().to_vec(),
            Opcode::JumpNotTruthy(o) => o.to_bytes().to_vec(),
            Opcode::Jump(o) => o.to_bytes().to_vec(),
            Opcode::Null(o) => o.to_bytes().to_vec(),
            Opcode::GetGlobal(o) => o.to_bytes().to_vec(),
            Opcode::SetGlobal(o) => o.to_bytes().to_vec(),
            Opcode::Array(o) => o.to_bytes().to_vec(),
            Opcode::Hash(o) => o.to_bytes().to_vec(),
            Opcode::Index(o) => o.to_bytes().to_vec(),
            Opcode::Call(o) => o.to_bytes().to_vec(),
            Opcode::ReturnValue(o) => o.to_bytes().to_vec(),
            Opcode::Return(o) => o.to_bytes().to_vec(),
            Opcode::GetLocal(o) => o.to_bytes().to_vec(),
            Opcode::SetLocal(o) => o.to_bytes().to_vec(),
            Opcode::GetBuiltin(o) => o.to_bytes().to_vec(),
            Opcode::Closure(o) => o.to_bytes().to_vec(),
            Opcode::GetFree(o) => o.to_bytes().to_vec(),
            Opcode::CurrentClosure(o) => o.to_bytes().to_vec(),
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
            Opcode::Minus(o) => o.readsize(),
            Opcode::Bang(o) => o.readsize(),
            Opcode::JumpNotTruthy(o) => o.readsize(),
            Opcode::Jump(o) => o.readsize(),
            Opcode::Null(o) => o.readsize(),
            Opcode::GetGlobal(o) => o.readsize(),
            Opcode::SetGlobal(o) => o.readsize(),
            Opcode::Array(o) => o.readsize(),
            Opcode::Hash(o) => o.readsize(),
            Opcode::Index(o) => o.readsize(),
            Opcode::Call(o) => o.readsize(),
            Opcode::ReturnValue(o) => o.readsize(),
            Opcode::Return(o) => o.readsize(),
            Opcode::GetLocal(o) => o.readsize(),
            Opcode::SetLocal(o) => o.readsize(),
            Opcode::GetBuiltin(o) => o.readsize(),
            Opcode::Closure(o) => o.readsize(),
            Opcode::GetFree(o) => o.readsize(),
            Opcode::CurrentClosure(o) => o.readsize(),
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

impl From<Minus> for Opcode {
    fn from(value: Minus) -> Self {
        Opcode::Minus(value)
    }
}

impl From<Bang> for Opcode {
    fn from(value: Bang) -> Self {
        Opcode::Bang(value)
    }
}

impl From<JumpNotTruthy> for Opcode {
    fn from(value: JumpNotTruthy) -> Self {
        Opcode::JumpNotTruthy(value)
    }
}

impl From<Jump> for Opcode {
    fn from(value: Jump) -> Self {
        Opcode::Jump(value)
    }
}

impl From<Null> for Opcode {
    fn from(value: Null) -> Self {
        Opcode::Null(value)
    }
}

impl From<GetGlobal> for Opcode {
    fn from(value: GetGlobal) -> Self {
        Opcode::GetGlobal(value)
    }
}

impl From<SetGlobal> for Opcode {
    fn from(value: SetGlobal) -> Self {
        Opcode::SetGlobal(value)
    }
}

impl From<Array> for Opcode {
    fn from(value: Array) -> Self {
        Opcode::Array(value)
    }
}

impl From<Hash> for Opcode {
    fn from(value: Hash) -> Self {
        Opcode::Hash(value)
    }
}

impl From<Index> for Opcode {
    fn from(value: Index) -> Self {
        Opcode::Index(value)
    }
}

impl From<Call> for Opcode {
    fn from(value: Call) -> Self {
        Opcode::Call(value)
    }
}

impl From<ReturnValue> for Opcode {
    fn from(value: ReturnValue) -> Self {
        Opcode::ReturnValue(value)
    }
}

impl From<Return> for Opcode {
    fn from(value: Return) -> Self {
        Opcode::Return(value)
    }
}

impl From<GetLocal> for Opcode {
    fn from(value: GetLocal) -> Self {
        Opcode::GetLocal(value)
    }
}

impl From<SetLocal> for Opcode {
    fn from(value: SetLocal) -> Self {
        Opcode::SetLocal(value)
    }
}

impl From<GetBuiltin> for Opcode {
    fn from(value: GetBuiltin) -> Self {
        Opcode::GetBuiltin(value)
    }
}

impl From<Closure> for Opcode {
    fn from(value: Closure) -> Self {
        Opcode::Closure(value)
    }
}

impl From<GetFree> for Opcode {
    fn from(value: GetFree) -> Self {
        Opcode::GetFree(value)
    }
}

impl From<CurrentClosure> for Opcode {
    fn from(value: CurrentClosure) -> Self {
        Opcode::CurrentClosure(value)
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
            OperandType::Minus => Ok(Minus.into()),
            OperandType::Bang => Ok(Bang.into()),
            OperandType::JumpNotTruthy => {
                Ok(JumpNotTruthy(JumpNotTruthy::try_read(&value[1..])?).into())
            }
            OperandType::Jump => Ok(Jump(Jump::try_read(&value[1..])?).into()),
            OperandType::Null => Ok(Null.into()),
            OperandType::GetGlobal => Ok(GetGlobal(GetGlobal::try_read(&value[1..])?).into()),
            OperandType::SetGlobal => Ok(SetGlobal(SetGlobal::try_read(&value[1..])?).into()),
            OperandType::Array => Ok(Array(Array::try_read(&value[1..])?).into()),
            OperandType::Hash => Ok(Hash(Hash::try_read(&value[1..])?).into()),
            OperandType::Index => Ok(Index.into()),
            OperandType::Call => Ok(Call(Call::try_read(&value[1..])?).into()),
            OperandType::ReturnValue => Ok(ReturnValue.into()),
            OperandType::Return => Ok(Return.into()),
            OperandType::GetLocal => Ok(GetLocal(GetLocal::try_read(&value[1..])?).into()),
            OperandType::SetLocal => Ok(SetLocal(SetLocal::try_read(&value[1..])?).into()),
            OperandType::GetBuiltin => Ok(GetBuiltin(GetBuiltin::try_read(&value[1..])?).into()),
            OperandType::Closure => {
                let res = Closure::try_read(&value[1..])?;
                Ok(Closure(res.0, res.1).into())
            }
            OperandType::GetFree => Ok(GetFree(GetFree::try_read(&value[1..])?).into()),
            OperandType::CurrentClosure => Ok(CurrentClosure.into()),
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
            Self::Minus(o) => write!(f, "{}", o),
            Self::Bang(o) => write!(f, "{}", o),
            Self::JumpNotTruthy(o) => write!(f, "{}", o),
            Self::Jump(o) => write!(f, "{}", o),
            Self::Null(o) => write!(f, "{}", o),
            Self::GetGlobal(o) => write!(f, "{}", o),
            Self::SetGlobal(o) => write!(f, "{}", o),
            Self::Array(o) => write!(f, "{}", o),
            Self::Hash(o) => write!(f, "{}", o),
            Self::Index(o) => write!(f, "{}", o),
            Self::Call(o) => write!(f, "{}", o),
            Self::ReturnValue(o) => write!(f, "{}", o),
            Self::Return(o) => write!(f, "{}", o),
            Self::GetLocal(o) => write!(f, "{}", o),
            Self::SetLocal(o) => write!(f, "{}", o),
            Self::GetBuiltin(o) => write!(f, "{}", o),
            Self::Closure(o) => write!(f, "{}", o),
            Self::GetFree(o) => write!(f, "{}", o),
            Self::CurrentClosure(o) => write!(f, "{}", o),
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
