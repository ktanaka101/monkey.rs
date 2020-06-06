use std::fmt;
use std::fmt::{Display, Formatter};

#[derive(Debug, Default, PartialEq)]
pub struct Instructions(pub Vec<u8>);

impl From<Vec<u8>> for Instructions {
    fn from(value: Vec<u8>) -> Self {
        Instructions(value)
    }
}

impl From<OpConstant> for Instructions {
    fn from(value: OpConstant) -> Self {
        Instructions(value.to_bytes().to_vec())
    }
}

impl From<Instructions> for Vec<u8> {
    fn from(value: Instructions) -> Self {
        value.0
    }
}

impl From<Vec<Opcode>> for Instructions {
    fn from(value: Vec<Opcode>) -> Self {
        value
            .into_iter()
            .flat_map(|v| v.to_bytes())
            .collect::<Vec<_>>()
            .into()
    }
}

impl Display for Instructions {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "",)
    }
}

impl From<Vec<Instructions>> for Instructions {
    fn from(value: Vec<Instructions>) -> Self {
        value
            .into_iter()
            .flat_map(|v| v.0.to_vec())
            .collect::<Vec<_>>()
            .into()
    }
}

#[derive(Debug)]
pub struct Definition {
    pub name: String,
    pub operand_widths: Vec<i32>,
}

#[derive(Debug)]
pub struct OpConstant(pub u16);
impl OpConstant {
    pub const fn code() -> u8 {
        0
    }

    pub fn to_bytes(&self) -> [u8; 3] {
        let mut v = [0; 3];
        v[0] = Self::code();
        let v2 = self.0.to_be_bytes();
        v[1] = v2[0];
        v[2] = v2[1];
        v
    }

    pub fn read(bytes: [u8; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}

impl From<u16> for OpConstant {
    fn from(value: u16) -> Self {
        OpConstant(value)
    }
}

#[derive(Debug)]
pub enum Opcode {
    OpConstant(OpConstant),
}

impl Opcode {
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Opcode::OpConstant(o) => o.to_bytes().to_vec(),
        }
    }
}

impl From<OpConstant> for Opcode {
    fn from(value: OpConstant) -> Self {
        Opcode::OpConstant(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_bytes() {
        let tests = vec![(
            OpConstant(65534).to_bytes().to_vec(),
            vec![OpConstant::code(), 255, 254],
        )];

        tests.into_iter().for_each(|(bytes, expected_bytes)| {
            assert_eq!(bytes.to_vec(), expected_bytes);
        });
    }
}
