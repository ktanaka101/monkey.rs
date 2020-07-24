use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Call(pub u8);

impl OperandCode for Call {
    const TYPE: OperandType = OperandType::Call;
    const NAME: &'static str = "Call";
}

impl Display for Call {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl vm::convert::Read<u8, 1> for Call {
    fn read(bytes: [vm::bytecode::Instruction; 1]) -> u8 {
        u8::from_be_bytes(bytes)
    }
}
