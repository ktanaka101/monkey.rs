use crate::vm;

// TODO: Remove "TARGET" after the expression is supported
pub trait ToBytes<const SIZE: usize, const TARGET_SIZE: usize>
where
    Self: vm::opcode::OperandCode,
{
    fn to_bytes(&self) -> [vm::bytecode::Instruction; SIZE] {
        let mut v: [vm::bytecode::Instruction; SIZE] = [0; SIZE];
        v[0] = Self::TYPE.into();
        let v2: [vm::bytecode::Instruction; TARGET_SIZE] = self.target_to_bytes();
        for i in 0..TARGET_SIZE {
            v[i + 1] = v2[i];
        }

        v
    }

    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; TARGET_SIZE];

    fn bytesize() -> usize {
        SIZE
    }
}

impl ToBytes<3, 2> for vm::opcode::Constant {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<1, 0> for vm::opcode::Add {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Pop {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Sub {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Mul {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Div {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::True {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::False {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Equal {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::NotEqual {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::GreaterThan {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Minus {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Bang {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<3, 2> for vm::opcode::JumpNotTruthy {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<3, 2> for vm::opcode::Jump {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<1, 0> for vm::opcode::Null {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_bytes() {
        let tests: Vec<(vm::opcode::Opcode, Vec<u8>)> = vec![
            (vm::opcode::Constant(65534).into(), vec![0, 255, 254]),
            (vm::opcode::Add.into(), vec![1]),
            (vm::opcode::Sub.into(), vec![3]),
            (vm::opcode::Mul.into(), vec![4]),
            (vm::opcode::Div.into(), vec![5]),
            (vm::opcode::Pop.into(), vec![2]),
            (vm::opcode::True.into(), vec![6]),
            (vm::opcode::False.into(), vec![7]),
            (vm::opcode::Equal.into(), vec![8]),
            (vm::opcode::NotEqual.into(), vec![9]),
            (vm::opcode::GreaterThan.into(), vec![10]),
            (vm::opcode::Minus.into(), vec![11]),
            (vm::opcode::Bang.into(), vec![12]),
            (vm::opcode::JumpNotTruthy(65534).into(), vec![13, 255, 254]),
            (vm::opcode::Jump(65534).into(), vec![14, 255, 254]),
            (vm::opcode::Null.into(), vec![15]),
        ];

        tests.into_iter().for_each(|(bytes, expected_bytes)| {
            assert_eq!(bytes.to_bytes().to_vec(), expected_bytes);
        });
    }
}
