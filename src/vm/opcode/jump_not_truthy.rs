use super::preludes::*;

#[derive(Debug, Clone)]
pub struct JumpNotTruthy(pub u16);

impl OperandCode for JumpNotTruthy {
    const TYPE: OperandType = OperandType::JumpNotTruthy;
    const NAME: &'static str = "JumpNotTruthy";
}

impl Display for JumpNotTruthy {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name(), self.0)
    }
}

impl vm::convert::Read<u16, 2> for JumpNotTruthy {
    fn read(bytes: [vm::bytecode::Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}
