use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Call {
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

impl TryFrom<Expr> for Call {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Call(call) => Ok(call),
            expr => Err(ParserError::Convert(format!("{:?}", expr), "Call".into()).into()),
        }
    }
}
