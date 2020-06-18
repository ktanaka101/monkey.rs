use super::preludes::*;

#[derive(Debug, Clone)]
pub struct GetGlobal(pub u16);

impl From<u16> for GetGlobal {
    fn from(value: u16) -> Self {
        GetGlobal(value)
    }
}

impl Display for GetGlobal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for GetGlobal {
    const TYPE: OperandType = OperandType::GetGlobal;
    const NAME: &'static str = "GetGlobal";
}

impl vm::convert::Read<u16, 2> for GetGlobal {
    fn read(bytes: [vm::bytecode::Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}
