use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub return_value: Expr,
}

impl Return {
    const fn literal() -> &'static str {
        "return"
    }
}

impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!("{} {};", Self::literal(), self.return_value);
        write!(f, "{}", out)
    }
}
