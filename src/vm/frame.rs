use super::preludes::*;

use std::cell::RefCell;
use std::rc::Rc;

use crate::evaluator::object;
use vm::bytecode;

pub const MAX_FRAMES: usize = 1024;

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Frame {
    pub func: object::CompiledFunction,
    pub pointer: usize,
    pub base_pointer: usize,
}

impl Frame {
    pub fn new(func: object::CompiledFunction, base_pointer: usize) -> Self {
        Self {
            func,
            pointer: 0,
            base_pointer,
        }
    }

    pub fn instructions(&self) -> &bytecode::Instructions {
        &self.func.instructions
    }
}

impl From<Frame> for bytecode::Instructions {
    fn from(value: Frame) -> Self {
        value.func.instructions
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct StackFrame {
    frames: Vec<Rc<RefCell<Frame>>>,
    pointer: usize,
}

impl Default for StackFrame {
    fn default() -> Self {
        Self {
            frames: vec![Rc::new(RefCell::new(Frame::default())); MAX_FRAMES],
            pointer: 0,
        }
    }
}

impl StackFrame {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn current(&self) -> Rc<RefCell<Frame>> {
        Rc::clone(&self.frames[self.pointer - 1])
    }

    pub fn push(&mut self, frame: Frame) {
        self.frames[self.pointer] = Rc::new(RefCell::new(frame));
        self.pointer += 1;
    }

    pub fn pop(&mut self) -> Rc<RefCell<Frame>> {
        self.pointer -= 1;
        Rc::clone(&self.frames[self.pointer])
    }
}
