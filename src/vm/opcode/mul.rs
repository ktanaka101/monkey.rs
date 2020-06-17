use super::preludes::*;

#[derive(Debug, Clone)]
pub struct Mul;

impl OperandCode for Mul {
    const TYPE: OperandType = OperandType::Mul;
    const NAME: &'static str = "Mul";
}

impl Display for Mul {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Mul {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
