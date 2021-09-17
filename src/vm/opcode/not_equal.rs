use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct NotEqual;

impl OperandCode for NotEqual {
    const TYPE: OperandType = OperandType::NotEqual;
    const NAME: &'static str = "NotEqual";
}

impl Display for NotEqual {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for NotEqual {
    fn read(_: [vm::bytecode::Instruction; 0]) {
        
    }
}
