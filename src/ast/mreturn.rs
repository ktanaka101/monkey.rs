use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub token: Token,
    pub return_value: Expr,
}

impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!("{} {};", self.token.literal, self.return_value);
        write!(f, "{}", out)
    }
}
