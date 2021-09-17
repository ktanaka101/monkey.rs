use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Sub;

impl OperandCode for Sub {
    const TYPE: OperandType = OperandType::Sub;
    const NAME: &'static str = "Sub";
}

impl Display for Sub {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Sub {
    fn read(_: [vm::bytecode::Instruction; 0]) {}
}
