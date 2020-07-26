use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub params: Vec<Identifier>,
    pub body: Block,
    pub name: String,
}

impl Function {
    const fn literal() -> &'static str {
        "fn"
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!(
            "{} {}({}) {}",
            Self::literal(),
            self.name,
            self.params
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.body
        );

        write!(f, "{}", out)
    }
}

impl TryFrom<Expr> for Function {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::Function(func) => Ok(func),
            expr => Err(ParserError::Convert(
                format!("{:?}", expr),
                "Function".into(),
            ))?,
        }
    }
}
