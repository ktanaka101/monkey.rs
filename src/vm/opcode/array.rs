use super::preludes::*;

#[derive(Debug, Clone)]
pub struct Array(pub u16);

impl From<u16> for Array {
    fn from(value: u16) -> Self {
        Array(value)
    }
}

impl Display for Array {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for Array {
    const TYPE: OperandType = OperandType::Array;
    const NAME: &'static str = "Array";
}

impl vm::convert::Read<u16, 2> for Array {
    fn read(bytes: [vm::bytecode::Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}
