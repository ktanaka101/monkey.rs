use crate::vm;

// TODO: Remove "TARGET" after the expression is supported
pub trait ToBytes<const SIZE: usize, const TARGET_SIZE: usize>
where
    Self: vm::opcode::OperandCode,
{
    fn to_bytes(&self) -> [vm::bytecode::Instruction; SIZE] {
        let mut v: [vm::bytecode::Instruction; SIZE] = [0; SIZE];
        v[0] = Self::code();
        let v2: [vm::bytecode::Instruction; TARGET_SIZE] = self.target_to_bytes();
        for i in 0..TARGET_SIZE {
            v[i + 1] = v2[i];
        }

        v
    }

    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; TARGET_SIZE];
}

impl ToBytes<3, 2> for vm::opcode::Constant {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

#[cfg(test)]
mod tests {
    use vm::opcode::OperandCode;

    use super::*;

    #[test]
    fn test_to_bytes() {
        let tests = vec![(
            vm::opcode::Constant(65534).to_bytes().to_vec(),
            vec![0, 255, 254],
        )];

        tests.into_iter().for_each(|(bytes, expected_bytes)| {
            assert_eq!(bytes.to_vec(), expected_bytes);
        });
    }
}
