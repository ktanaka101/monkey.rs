use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Array {
    pub elements: Vec<Expr>,
}

impl Display for Array {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .elements
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<String>>()
            .join(", ");

        write!(f, "[{}]", out)
    }
}
