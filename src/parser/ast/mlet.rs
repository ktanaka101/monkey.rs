use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Let {
    pub name: Identifier,
    pub value: Expr,
}

impl Display for Let {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!("{} {} = {};", self.name, self.name, self.value);

        write!(f, "{}", out)
    }
}

impl TryFrom<Stmt> for Let {
    type Error = Error;

    fn try_from(value: Stmt) -> Result<Self> {
        match value {
            Stmt::Let(mlet) => Ok(mlet),
            stmt => Err(ParserError::Convert(format!("{:?}", stmt), "Let".into()))?,
        }
    }
}
