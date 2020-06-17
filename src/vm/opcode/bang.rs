use super::preludes::*;

#[derive(Debug, Clone)]
pub struct Bang;

impl OperandCode for Bang {
    const TYPE: OperandType = OperandType::Bang;
    const NAME: &'static str = "Bang";
}

impl Display for Bang {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Bang {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
