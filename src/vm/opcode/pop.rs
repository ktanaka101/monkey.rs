use super::preludes::*;

#[derive(Debug, Clone)]
pub struct Pop;

impl OperandCode for Pop {
    const TYPE: OperandType = OperandType::Pop;
    const NAME: &'static str = "Pop";
}

impl Display for Pop {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Pop {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
