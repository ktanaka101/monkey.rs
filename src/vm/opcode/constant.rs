use super::preludes::*;

#[derive(Debug)]
pub struct Constant(pub u16);

impl From<u16> for Constant {
    fn from(value: u16) -> Self {
        Constant(value)
    }
}

impl Display for Constant {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", Self::name(), self.0)
    }
}

impl OperandCode for Constant {
    const CODE: u8 = 0;
    fn name() -> &'static str {
        "Constant"
    }
}

impl vm::convert::Read<u16, 2> for Constant {
    fn read(bytes: [vm::bytecode::Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}
