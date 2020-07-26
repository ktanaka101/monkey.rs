use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct GetBuiltin(pub u8);

impl From<u8> for GetBuiltin {
    fn from(value: u8) -> Self {
        GetBuiltin(value)
    }
}

impl Display for GetBuiltin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for GetBuiltin {
    const TYPE: OperandType = OperandType::GetBuiltin;
    const NAME: &'static str = "GetBuiltin";
}

impl vm::convert::Read<u8, 1> for GetBuiltin {
    fn read(bytes: [vm::bytecode::Instruction; 1]) -> u8 {
        u8::from_be_bytes(bytes)
    }
}
