use super::preludes::*;

#[derive(Debug)]
pub struct True;

impl OperandCode for True {
    const TYPE: OperandType = OperandType::True;
    const NAME: &'static str = "True";
}

impl Display for True {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for True {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
