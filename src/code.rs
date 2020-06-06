use std::fmt;
use std::fmt::{Display, Formatter};

use anyhow::Result;

pub type Instruction = u8;

#[derive(Debug, Default, PartialEq)]
pub struct Instructions(pub Vec<Instruction>);

impl From<Vec<Instruction>> for Instructions {
    fn from(value: Vec<Instruction>) -> Self {
        Instructions(value)
    }
}

impl From<OpConstant> for Instructions {
    fn from(value: OpConstant) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<Instructions> for Vec<Instruction> {
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
        let mut pos = 0;
        let mut buf = String::new();

        while pos < self.0.len() {
            let read = OpConstant::try_read(&self.0[pos + 1..]);
            let msg = match read {
                Ok(read) => format!("{:>04} {} {}¥n", pos, OpConstant::name(), read),
                Err(e) => format!("{:>04} {} Error: {}¥n", pos, OpConstant::name(), e),
            };
            buf.push_str(msg.as_str());
            pos = pos + 1 + usize::from(OpConstant::readsize());
        }

        write!(f, "{}", buf)
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

pub trait Read<T, const SIZE: usize> {
    fn read(bytes: [Instruction; SIZE]) -> T;
    fn readsize() -> usize {
        SIZE
    }
}

pub trait TryRead<T, const SIZE: usize>
where
    Self: Read<T, SIZE>,
{
    fn try_read(bytes: &[Instruction]) -> Result<T> {
        if bytes.len() < SIZE {
            Err(anyhow::format_err!("expected bytes length <= {}", SIZE))?
        }

        let mut b: [Instruction; SIZE] = [0; SIZE];
        for i in 0..SIZE {
            b[i] = bytes[i];
        }

        Ok(Self::read(b))
    }
}

// TODO: Remove "TARGET" after the expression is supported
pub trait ToBytes<const SIZE: usize, const TARGET_SIZE: usize>
where
    Self: OperandCode,
{
    fn to_bytes(&self) -> [Instruction; SIZE] {
        let mut v: [Instruction; SIZE] = [0; SIZE];
        v[0] = Self::code();
        let v2: [Instruction; TARGET_SIZE] = self.target_to_bytes();
        for i in 0..TARGET_SIZE {
            v[i + 1] = v2[i];
        }

        v
    }

    fn target_to_bytes(&self) -> [Instruction; TARGET_SIZE];
}

pub trait OperandCode {
    const CODE: u8;
    fn code() -> u8 {
        Self::CODE
    }
    fn name() -> &'static str;
}

#[derive(Debug)]
pub struct OpConstant(pub u16);

impl OperandCode for OpConstant {
    const CODE: u8 = 0;
    fn name() -> &'static str {
        "OpConstant"
    }
}

impl ToBytes<3, 2> for OpConstant {
    fn target_to_bytes(&self) -> [Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl Read<u16, 2> for OpConstant {
    fn read(bytes: [Instruction; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }
}

impl<T: Read<U, S>, U, const S: usize> TryRead<U, S> for T {}

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

    #[test]
    fn test_format_instructions() {
        let tests = vec![
            (
                vec![OpConstant(65534), OpConstant(1)],
                "0000 OpConstant 65534¥n0003 OpConstant 1¥n",
            ),
            (vec![OpConstant(65534)], "0000 OpConstant 65534¥n"),
        ];

        tests.into_iter().for_each(|(input, expected)| {
            let instructions: Instructions = input
                .into_iter()
                .flat_map(|v| v.to_bytes().to_vec())
                .collect::<Vec<Instruction>>()
                .into();
            assert_eq!(format!("{}", instructions), expected);
        });
    }
}
