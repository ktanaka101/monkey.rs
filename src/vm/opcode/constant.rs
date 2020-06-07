use super::preludes::*;

#[derive(Debug)]
pub struct OpConstant(pub u16);

impl From<u16> for OpConstant {
    fn from(value: u16) -> Self {
        OpConstant(value)
    }
}

impl vm::opcode::OperandCode for OpConstant {
    const CODE: u8 = 0;
    fn name() -> &'static str {
        "OpConstant"
    }
}

impl vm::convert::Read<u16, 2> for OpConstant {
    fn read(bytes: [vm::bytecode::Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}
