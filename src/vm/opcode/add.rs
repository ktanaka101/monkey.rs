use super::preludes::*;

#[derive(Debug)]
pub struct Add;

impl OperandCode for Add {
    const CODE: u8 = 1;
    fn name() -> &'static str {
        "Add"
    }
}

impl Display for Add {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::name())
    }
}

impl vm::convert::Read<(), 0> for Add {
    fn read(_: [vm::bytecode::Instruction; 0]) -> () {
        ()
    }
}
