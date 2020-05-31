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
