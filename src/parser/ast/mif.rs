use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct If {
    pub cond: Box<Expr>,
    pub consequence: Block,
    pub alternative: Option<Block>,
}

impl Display for If {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut out = format!("if {} {}", self.cond, self.consequence);
        if let Some(alt) = &self.alternative {
            out.push_str(&format!(" else {}", alt));
        }

        write!(f, "{}", out)
    }
}

impl TryFrom<Expr> for If {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self> {
        match value {
            Expr::If(mif) => Ok(mif),
            expr => Err(ParserError::Convert(format!("{:?}", expr), "If".into()).into()),
        }
    }
}
