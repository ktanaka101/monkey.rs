use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Return;

impl OperandCode for Return {
    const TYPE: OperandType = OperandType::Return;
    const NAME: &'static str = "Return";
}

impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Return {
    fn read(_: [vm::bytecode::Instruction; 0]) {}
}
