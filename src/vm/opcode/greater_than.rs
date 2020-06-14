use super::preludes::*;

#[derive(Debug)]
pub struct GreaterThan;

impl OperandCode for GreaterThan {
    const TYPE: OperandType = OperandType::GreaterThan;
    const NAME: &'static str = "GreaterThan";
}

impl Display for GreaterThan {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for GreaterThan {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
