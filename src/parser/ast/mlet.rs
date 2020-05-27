use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Let {
    pub name: Identifier,
    pub value: Expr,
}

impl Display for Let {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!("{} {} = {};", self.name, self.name, self.value);

        write!(f, "{}", out)
    }
}
