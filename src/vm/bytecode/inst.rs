use super::preludes::*;

use vm::compiler::convert::ToBytes;
use vm::convert::{Read, TryRead};
use vm::opcode;
use vm::opcode::OperandCode;

pub type Instruction = u8;

#[derive(Debug, Default, PartialEq, Clone)]
pub struct Instructions(pub Vec<Instruction>);

impl From<Vec<Instruction>> for Instructions {
    fn from(value: Vec<Instruction>) -> Self {
        Instructions(value)
    }
}

impl From<opcode::Constant> for Instructions {
    fn from(value: opcode::Constant) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<Instructions> for Vec<Instruction> {
    fn from(value: Instructions) -> Self {
        value.0
    }
}

impl From<Vec<opcode::Opcode>> for Instructions {
    fn from(value: Vec<opcode::Opcode>) -> Self {
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
            let read = opcode::Constant::try_read(&self.0[pos + 1..]);
            let msg = match read {
                Ok(read) => format!("{:>04} {} {}¥n", pos, opcode::Constant::name(), read),
                Err(e) => format!("{:>04} {} Error: {}¥n", pos, opcode::Constant::name(), e),
            };
            buf.push_str(msg.as_str());
            pos = pos + 1 + usize::from(opcode::Constant::readsize());
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_format_instructions() {
        let tests = vec![
            (
                vec![opcode::Constant(65534), opcode::Constant(1)],
                "0000 Constant 65534¥n0003 Constant 1¥n",
            ),
            (vec![opcode::Constant(65534)], "0000 Constant 65534¥n"),
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
