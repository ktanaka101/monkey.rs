use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct False;

impl OperandCode for False {
    const TYPE: OperandType = OperandType::False;
    const NAME: &'static str = "False";
}

impl Display for False {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for False {
    fn read(_: [vm::bytecode::Instruction; 0]) {}
}
