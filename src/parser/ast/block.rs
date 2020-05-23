use super::prelude::*;
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub token: Token,
    pub statements: Vec<Stmt>,
}

impl Display for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.statements
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<String>>()
                .join("")
        )
    }
}
