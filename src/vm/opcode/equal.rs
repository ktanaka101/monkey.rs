use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Equal;

impl OperandCode for Equal {
    const TYPE: OperandType = OperandType::Equal;
    const NAME: &'static str = "Equal";
}

impl Display for Equal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Equal {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
