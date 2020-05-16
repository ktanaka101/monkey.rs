use super::prelude::*;
use super::Object;

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub value: Box<Object>,
}
impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
