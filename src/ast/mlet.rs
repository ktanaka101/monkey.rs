use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Let {
    pub token: Token,
    pub name: Identifier,
    pub value: Expr,
}

impl Display for Let {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!("{} {} = {};", self.token.literal, self.name, self.value);

        write!(f, "{}", out)
    }
}
