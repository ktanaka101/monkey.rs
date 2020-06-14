use super::preludes::*;

#[derive(Debug)]
pub struct Minus;

impl OperandCode for Minus {
    const TYPE: OperandType = OperandType::Minus;
    const NAME: &'static str = "Minus";
}

impl Display for Minus {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Minus {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
