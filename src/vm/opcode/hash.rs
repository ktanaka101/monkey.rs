use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Hash(pub u16);

impl From<u16> for Hash {
    fn from(value: u16) -> Self {
        Hash(value)
    }
}

impl Display for Hash {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl OperandCode for Hash {
    const TYPE: OperandType = OperandType::Hash;
    const NAME: &'static str = "Hash";
}

impl vm::convert::Read<u16, 2> for Hash {
    fn read(bytes: [vm::bytecode::Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}
