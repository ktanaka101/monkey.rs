use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Closure(pub u16, pub u8);

impl Display for Closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.name(), self.0, self.1)
    }
}

impl OperandCode for Closure {
    const TYPE: OperandType = OperandType::Closure;
    const NAME: &'static str = "Closure";
}

impl vm::convert::Read<(u16, u8), 3> for Closure {
    fn read(bytes: [vm::bytecode::Instruction; 3]) -> (u16, u8) {
        (u16::from_be_bytes([bytes[0], bytes[1]]), bytes[2])
    }
}
