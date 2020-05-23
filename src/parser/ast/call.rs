use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Call {
    pub token: Token,
    pub func: Box<Expr>,
    pub args: Vec<Expr>,
}

impl Display for Call {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!(
            "{}({})",
            self.func,
            self.args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        );

        write!(f, "{}", out)
    }
}
