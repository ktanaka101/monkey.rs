use super::preludes::*;

#[derive(Debug, Clone)]
pub struct Call;

impl OperandCode for Call {
    const TYPE: OperandType = OperandType::Call;
    const NAME: &'static str = "Call";
}

impl Display for Call {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Call {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
