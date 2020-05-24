use super::prelude::*;

#[derive(Debug, Default, PartialEq, Clone)]
pub struct Program {
    pub statements: Vec<Stmt>,
}

impl Display for Program {
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
