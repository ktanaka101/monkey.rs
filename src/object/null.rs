use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Null();
impl Display for Null {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "null")
    }
}
