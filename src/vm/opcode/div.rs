use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct Div;

impl OperandCode for Div {
    const TYPE: OperandType = OperandType::Div;
    const NAME: &'static str = "Div";
}

impl Display for Div {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for Div {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
