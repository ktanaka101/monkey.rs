use super::preludes::*;

use vm::convert::ToBytes;
use vm::opcode;

pub type Instruction = u8;

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
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

impl From<opcode::JumpNotTruthy> for Instructions {
    fn from(value: opcode::JumpNotTruthy) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::Jump> for Instructions {
    fn from(value: opcode::Jump) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::GetGlobal> for Instructions {
    fn from(value: opcode::GetGlobal) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::SetGlobal> for Instructions {
    fn from(value: opcode::SetGlobal) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::Array> for Instructions {
    fn from(value: opcode::Array) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::Hash> for Instructions {
    fn from(value: opcode::Hash) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::GetLocal> for Instructions {
    fn from(value: opcode::GetLocal) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::SetLocal> for Instructions {
    fn from(value: opcode::SetLocal) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::Call> for Instructions {
    fn from(value: opcode::Call) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::GetBuiltin> for Instructions {
    fn from(value: opcode::GetBuiltin) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::Closure> for Instructions {
    fn from(value: opcode::Closure) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl From<opcode::GetFree> for Instructions {
    fn from(value: opcode::GetFree) -> Self {
        value.to_bytes().to_vec().into()
    }
}

impl<T: ToBytes<1, 0>> From<T> for Instructions {
    fn from(value: T) -> Self {
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
                    pos = pos + 1 + op.readsize();
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
            opcode::Sub.into(),
            opcode::Mul.into(),
            opcode::Div.into(),
            opcode::Equal.into(),
            opcode::NotEqual.into(),
            opcode::GreaterThan.into(),
            opcode::JumpNotTruthy(1).into(),
            opcode::Jump(2).into(),
            opcode::Null.into(),
            opcode::GetGlobal(65535).into(),
            opcode::SetGlobal(65535).into(),
            opcode::Array(65535).into(),
            opcode::Hash(65535).into(),
            opcode::Index.into(),
            opcode::Call(254).into(),
            opcode::ReturnValue.into(),
            opcode::Return.into(),
            opcode::GetLocal(254).into(),
            opcode::SetLocal(254).into(),
            opcode::GetBuiltin(254).into(),
            opcode::Closure(65535, 255).into(),
            opcode::GetFree(254).into(),
            opcode::CurrentClosure.into(),
        ];
        let instructions = Instructions::from(instructions);

        let expected = "\
            0000 Add¥n\
            0001 Constant 2¥n\
            0004 Constant 65535¥n\
            0007 Pop¥n\
            0008 Sub¥n\
            0009 Mul¥n\
            0010 Div¥n\
            0011 Equal¥n\
            0012 NotEqual¥n\
            0013 GreaterThan¥n\
            0014 JumpNotTruthy 1¥n\
            0017 Jump 2¥n\
            0020 Null¥n\
            0021 GetGlobal 65535¥n\
            0024 SetGlobal 65535¥n\
            0027 Array 65535¥n\
            0030 Hash 65535¥n\
            0033 Index¥n\
            0034 Call 254¥n\
            0036 ReturnValue¥n\
            0037 Return¥n\
            0038 GetLocal 254¥n\
            0040 SetLocal 254¥n\
            0042 GetBuiltin 254¥n\
            0044 Closure 65535 255¥n\
            0048 GetFree 254¥n\
            0050 CurrentClosure¥n";

        assert_eq!(instructions.to_string(), expected);
    }
}
