use super::prelude::*;
use crate::evaluator::objects;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Closure {
    pub func: objects::CompiledFunction,
    pub free: Vec<objects::Object>,
}

impl Display for Closure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out_free = self
            .free
            .iter()
            .map(|obj| obj.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "Closure[{} {}]", self.func, out_free)
    }
}
