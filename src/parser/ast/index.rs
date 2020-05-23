use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Index {
    pub token: Token,
    pub left: Box<Expr>,
    pub index: Box<Expr>,
}

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}
