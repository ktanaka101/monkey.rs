use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct GetLocal(pub u8);

impl From<u8> for GetLocal {
    fn from(value: u8) -> Self {
        GetLocal(value)
    }
}

impl Display for GetLocal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for GetLocal {
    const TYPE: OperandType = OperandType::GetLocal;
    const NAME: &'static str = "GetLocal";
}

impl vm::convert::Read<u8, 1> for GetLocal {
    fn read(bytes: [vm::bytecode::Instruction; 1]) -> u8 {
        u8::from_be_bytes(bytes)
    }
}
