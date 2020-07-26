use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct SetLocal(pub u8);

impl From<u8> for SetLocal {
    fn from(value: u8) -> Self {
        SetLocal(value)
    }
}

impl Display for SetLocal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for SetLocal {
    const TYPE: OperandType = OperandType::SetLocal;
    const NAME: &'static str = "SetLocal";
}

impl vm::convert::Read<u8, 1> for SetLocal {
    fn read(bytes: [vm::bytecode::Instruction; 1]) -> u8 {
        u8::from_be_bytes(bytes)
    }
}
