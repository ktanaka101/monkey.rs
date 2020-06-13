use super::preludes::*;

use vm::compiler::convert::ToBytes;
use vm::opcode;

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

impl From<opcode::Add> for Instructions {
    fn from(value: opcode::Add) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::Pop> for Instructions {
    fn from(value: opcode::Pop) -> Self {
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
            let op = opcode::Opcode::try_from(&self.0[pos..]);
            match &op {
                Ok(op) => {
                    let msg = format!("{:>04} {}¥n", pos, op);
                    buf.push_str(msg.as_str());
                    pos = pos + 1 + usize::from(op.readsize());
                }
                Err(e) => {
                    let msg = format!("{:>04} Error: {}¥n", pos, e);
                    buf.push_str(msg.as_str());
                    break;
                }
            };
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
    fn test_instructions_string() {
        let instructions: Vec<Instructions> = vec![
            opcode::Add.into(),
            opcode::Constant(2).into(),
            opcode::Constant(65535).into(),
            opcode::Pop.into(),
        ]
        .into();
        let instructions = Instructions::from(instructions);

        let expected = "\
            0000 Add¥n\
            0001 Constant 2¥n\
            0004 Constant 65535¥n\
            0007 Pop¥n";

        assert_eq!(instructions.to_string(), expected);
    }
}
