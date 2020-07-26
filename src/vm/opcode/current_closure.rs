use super::preludes::*;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
pub struct CurrentClosure;

impl OperandCode for CurrentClosure {
    const TYPE: OperandType = OperandType::CurrentClosure;
    const NAME: &'static str = "CurrentClosure";
}

impl Display for CurrentClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl vm::convert::Read<(), 0> for CurrentClosure {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
