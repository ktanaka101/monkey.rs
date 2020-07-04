use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct SetGlobal(pub u16);

impl From<u16> for SetGlobal {
    fn from(value: u16) -> Self {
        SetGlobal(value)
    }
}

impl Display for SetGlobal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for SetGlobal {
    const TYPE: OperandType = OperandType::SetGlobal;
    const NAME: &'static str = "SetGlobal";
}

impl vm::convert::Read<u16, 2> for SetGlobal {
    fn read(bytes: [vm::bytecode::Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}
