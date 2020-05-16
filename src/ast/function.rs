use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub token: Token,
    pub params: Vec<Identifier>,
    pub body: Block,
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!(
            "{}({}) {}",
            self.token.literal,
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
