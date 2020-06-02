pub type Instructions = Vec<u8>;

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
