use super::preludes::*;

use vm::bytecode;

pub trait Read<T, const SIZE: usize> {
    fn read(bytes: [bytecode::Instruction; SIZE]) -> T;
    fn readsize() -> usize {
        SIZE
    }
}

pub trait TryRead<T, const SIZE: usize>
where
    Self: Read<T, SIZE>,
{
    fn try_read(bytes: &[bytecode::Instruction]) -> Result<T> {
        if bytes.len() < SIZE {
            Err(anyhow::format_err!("expected bytes length >= {}", SIZE))?
        }

        let mut b: [bytecode::Instruction; SIZE] = [0; SIZE];
        for i in 0..SIZE {
            b[i] = bytes[i];
        }

        Ok(Self::read(b))
    }
}

impl<T: Read<U, S>, U, const S: usize> TryRead<U, S> for T {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::opcode;

    #[test]
    fn test_read_operands() {
        let tests = vec![(
            opcode::OpConstant::read,
            opcode::Opcode::from(opcode::OpConstant(65535)),
            65535,
        )];

        tests.into_iter().for_each(|(read, input, expected_value)| {
            let instructions = bytecode::Instructions::from(input.to_bytes());
            let read_value = read([instructions.0[1], instructions.0[2]]);
            assert_eq!(read_value, expected_value);
        });
    }
}
