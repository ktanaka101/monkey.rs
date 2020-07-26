use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Index;

impl OperandCode for Index {
    const TYPE: OperandType = OperandType::Index;
    const NAME: &'static str = "Index";
}

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Index {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
