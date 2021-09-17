use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Add;

impl OperandCode for Add {
    const TYPE: OperandType = OperandType::Add;
    const NAME: &'static str = "Add";
}

impl Display for Add {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Add {
    fn read(_: [vm::bytecode::Instruction; 0]) {
        
    }
}
