use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct MacroLit {
    pub params: Vec<Identifier>,
    pub body: Block,
}

impl MacroLit {
    const fn literal() -> &'static str {
        "macro"
    }
}

impl Display for MacroLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let params = self
            .params
            .iter()
            .map(|param| param.to_string())
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "{}({}) {}", Self::literal(), params, self.body)
    }
}

impl TryFrom<Expr> for MacroLit {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::MacroLit(m) => Ok(m),
            expr => Err(ParserError::Convert(
                format!("{:?}", expr),
                "MacroLit".into(),
            ))?,
        }
    }
}
