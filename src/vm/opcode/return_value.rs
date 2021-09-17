use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct ReturnValue;

impl OperandCode for ReturnValue {
    const TYPE: OperandType = OperandType::ReturnValue;
    const NAME: &'static str = "ReturnValue";
}

impl Display for ReturnValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for ReturnValue {
    fn read(_: [vm::bytecode::Instruction; 0]) {
        
    }
}
