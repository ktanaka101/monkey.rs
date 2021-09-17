use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Null;

impl OperandCode for Null {
    const TYPE: OperandType = OperandType::Null;
    const NAME: &'static str = "Null";
}

impl Display for Null {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Null {
    fn read(_: [vm::bytecode::Instruction; 0]) {}
}
