use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct GetFree(pub u8);

impl From<u8> for GetFree {
    fn from(value: u8) -> Self {
        GetFree(value)
    }
}

impl Display for GetFree {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for GetFree {
    const TYPE: OperandType = OperandType::GetFree;
    const NAME: &'static str = "GetFree";
}

impl vm::convert::Read<u8, 1> for GetFree {
    fn read(bytes: [vm::bytecode::Instruction; 1]) -> u8 {
        u8::from_be_bytes(bytes)
    }
}
