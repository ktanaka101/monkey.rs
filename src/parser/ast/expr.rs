use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Identifier(Identifier),
    PrefixExpr(PrefixExpr),
    InfixExpr(InfixExpr),
    If(If),
    Function(Function),
    Call(Call),
    Integer(Integer),
    Boolean(Boolean),
    StringLit(StringLit),
    Array(Array),
    Index(Index),
    Hash(Hash),
    MacroLit(MacroLit),
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Identifier(e) => write!(f, "{}", e),
            Self::PrefixExpr(e) => write!(f, "{}", e),
            Self::InfixExpr(e) => write!(f, "{}", e),
            Self::If(e) => write!(f, "{}", e),
            Self::Function(e) => write!(f, "{}", e),
            Self::Call(e) => write!(f, "{}", e),
            Self::Integer(e) => write!(f, "{}", e),
            Self::Boolean(e) => write!(f, "{}", e),
            Self::StringLit(e) => write!(f, "{}", e),
            Self::Array(e) => write!(f, "{}", e),
            Self::Index(e) => write!(f, "{}", e),
            Self::Hash(e) => write!(f, "{}", e),
            Self::MacroLit(e) => write!(f, "{}", e),
        }
    }
}

impl From<Identifier> for Expr {
    fn from(value: Identifier) -> Expr {
        Expr::Identifier(value)
    }
}

impl From<PrefixExpr> for Expr {
    fn from(value: PrefixExpr) -> Expr {
        Expr::PrefixExpr(value)
    }
}

impl From<InfixExpr> for Expr {
    fn from(value: InfixExpr) -> Expr {
        Expr::InfixExpr(value)
    }
}

impl From<If> for Expr {
    fn from(value: If) -> Expr {
        Expr::If(value)
    }
}

impl From<Function> for Expr {
    fn from(value: Function) -> Expr {
        Expr::Function(value)
    }
}

impl From<Call> for Expr {
    fn from(value: Call) -> Expr {
        Expr::Call(value)
    }
}

impl From<Integer> for Expr {
    fn from(value: Integer) -> Expr {
        Expr::Integer(value)
    }
}

impl From<Boolean> for Expr {
    fn from(value: Boolean) -> Expr {
        Expr::Boolean(value)
    }
}

impl From<StringLit> for Expr {
    fn from(value: StringLit) -> Expr {
        Expr::StringLit(value)
    }
}

impl From<Array> for Expr {
    fn from(value: Array) -> Expr {
        Expr::Array(value)
    }
}

impl From<Index> for Expr {
    fn from(value: Index) -> Expr {
        Expr::Index(value)
    }
}

impl From<Hash> for Expr {
    fn from(value: Hash) -> Expr {
        Expr::Hash(value)
    }
}

impl From<ExprStmt> for Expr {
    fn from(value: ExprStmt) -> Self {
        value.expr
    }
}

impl TryFrom<Node> for Expr {
    type Error = Error;
    fn try_from(value: Node) -> Result<Self> {
        match value {
            Node::Expr(expr) => Ok(expr),
            node => Err(ParserError::Convert(format!("{:?}", node), "Expr".into()).into()),
        }
    }
}
