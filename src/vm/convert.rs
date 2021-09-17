use super::preludes::*;

use vm::bytecode;

pub trait Read<T, const SIZE: usize> {
    fn read(bytes: [bytecode::Instruction; SIZE]) -> T;
    fn readsize(&self) -> usize {
        SIZE
    }
}

pub trait TryRead<T, const SIZE: usize>
where
    Self: Read<T, SIZE>,
{
    fn try_read(bytes: &[bytecode::Instruction]) -> Result<T> {
        if bytes.len() < SIZE {
            return Err(anyhow::format_err!("expected bytes length >= {}", SIZE));
        }

        let mut b: [bytecode::Instruction; SIZE] = [0; SIZE];
        b[..SIZE].clone_from_slice(&bytes[..SIZE]);

        Ok(Self::read(b))
    }
}

impl<T: Read<U, S>, U, const S: usize> TryRead<U, S> for T {}

// TODO: Remove "TARGET" after the expression is supported
pub trait ToBytes<const SIZE: usize, const TARGET_SIZE: usize>
where
    Self: vm::opcode::OperandCode,
{
    fn to_bytes(&self) -> [vm::bytecode::Instruction; SIZE] {
        let mut v: [vm::bytecode::Instruction; SIZE] = [0; SIZE];
        v[0] = Self::TYPE.into();
        let v2: [vm::bytecode::Instruction; TARGET_SIZE] = self.target_to_bytes();
        v[1..(TARGET_SIZE + 1)].clone_from_slice(&v2[..TARGET_SIZE]);

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

impl ToBytes<3, 2> for vm::opcode::GetGlobal {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<3, 2> for vm::opcode::SetGlobal {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<3, 2> for vm::opcode::Array {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<3, 2> for vm::opcode::Hash {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 2] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<1, 0> for vm::opcode::Index {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<2, 1> for vm::opcode::Call {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 1] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<1, 0> for vm::opcode::ReturnValue {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<1, 0> for vm::opcode::Return {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

impl ToBytes<2, 1> for vm::opcode::GetLocal {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 1] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<2, 1> for vm::opcode::SetLocal {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 1] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<2, 1> for vm::opcode::GetBuiltin {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 1] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<4, 3> for vm::opcode::Closure {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 3] {
        let bytes = self.0.to_be_bytes();
        [bytes[0], bytes[1], self.1.to_be_bytes()[0]]
    }
}

impl ToBytes<2, 1> for vm::opcode::GetFree {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 1] {
        self.0.to_be_bytes()
    }
}

impl ToBytes<1, 0> for vm::opcode::CurrentClosure {
    fn target_to_bytes(&self) -> [vm::bytecode::Instruction; 0] {
        [0; 0]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::opcode;

    #[test]
    fn test_read_operands() {
        let tests = vec![(
            opcode::Constant::read,
            opcode::Opcode::from(opcode::Constant(65535)),
            65535,
        )];

        tests.into_iter().for_each(|(read, input, expected_value)| {
            let instructions = bytecode::Instructions::from(input.to_bytes());
            let read_value = read([instructions.0[1], instructions.0[2]]);
            assert_eq!(read_value, expected_value);
        });
    }

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
            (vm::opcode::GetGlobal(65534).into(), vec![16, 255, 254]),
            (vm::opcode::SetGlobal(65534).into(), vec![17, 255, 254]),
            (vm::opcode::Array(65534).into(), vec![18, 255, 254]),
            (vm::opcode::Hash(65534).into(), vec![19, 255, 254]),
            (vm::opcode::Index.into(), vec![20]),
            (vm::opcode::Call(254).into(), vec![21, 254]),
            (vm::opcode::ReturnValue.into(), vec![22]),
            (vm::opcode::Return.into(), vec![23]),
            (vm::opcode::GetLocal(254).into(), vec![24, 254]),
            (vm::opcode::SetLocal(254).into(), vec![25, 254]),
            (vm::opcode::GetBuiltin(254).into(), vec![26, 254]),
            (
                vm::opcode::Closure(65533, 254).into(),
                vec![27, 255, 253, 254],
            ),
            (vm::opcode::GetFree(254).into(), vec![28, 254]),
            (vm::opcode::CurrentClosure.into(), vec![29]),
        ];

        tests.into_iter().for_each(|(bytes, expected_bytes)| {
            assert_eq!(bytes.to_bytes().to_vec(), expected_bytes);
        });
    }
}
