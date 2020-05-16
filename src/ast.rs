use crate::token::Token;
use std::fmt;
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq)]
pub enum Node {
    Program(Program),
    Stmt(Stmt),
    Expr(Expr),
}
impl Display for Node {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}
impl From<Program> for Node {
    fn from(node: Program) -> Self {
        Node::Program(node)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmt(ExprStmt),
    Let(Let),
    Return(Return),
    Block(Block),
}
impl From<Block> for Stmt {
    fn from(stmt: Block) -> Self {
        Stmt::Block(stmt)
    }
}
impl Display for Stmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

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
}
impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Debug, Default, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: Expr,
    pub token: Token,
}
impl Display for ExprStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.expr)
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct Let {
    pub token: Token,
    pub name: Identifier,
    pub value: Expr,
}
impl Display for Let {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!("{} {} = {};", self.token.literal, self.name, self.value);

        write!(f, "{}", out)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub token: Token,
    pub return_value: Expr,
}
impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!("{} {};", self.token.literal, self.return_value);
        write!(f, "{}", out)
    }
}

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
#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    pub token: Token,
    pub value: String,
}
impl Display for Identifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
#[derive(Debug, Clone, PartialEq)]
pub enum Operator {
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    Equal,
    NotEqual,
    Lt,
    Gt,
}
impl Display for Operator {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = match self {
            Self::Assign => "=",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Bang => "!",
            Self::Asterisk => "*",
            Self::Slash => "/",
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
        };
        write!(f, "{}", out)
    }
}
#[derive(Debug, Clone, PartialEq)]
pub struct PrefixExpr {
    pub token: Token,
    pub ope: Operator,
    pub right: Box<Expr>,
}
impl Display for PrefixExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}{})", self.ope, self.right.as_ref())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InfixExpr {
    pub token: Token,
    pub left: Box<Expr>,
    pub ope: Operator,
    pub right: Box<Expr>,
}
impl Display for InfixExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({} {} {})", self.left, self.ope, self.right)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct If {
    pub token: Token,
    pub cond: Box<Expr>,
    pub consequence: Block,
    pub alternative: Option<Block>,
}
impl Display for If {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut out = format!("if{} {}", self.cond, self.consequence);
        if let Some(alt) = &self.alternative {
            out.push_str(&format!("else {}", alt));
        }

        write!(f, "{}", out)
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub struct Call {
    pub token: Token,
    pub func: Box<Expr>,
    pub args: Vec<Expr>,
}
impl Display for Call {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = format!(
            "{}({})",
            self.func,
            self.args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        );

        write!(f, "{}", out)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Integer {
    pub token: Token,
    pub value: i64,
}
impl Display for Integer {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Boolean {
    pub token: Token,
    pub value: bool,
}
impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StringLit {
    pub token: Token,
    pub value: String,
}
impl Display for StringLit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.token.literal)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Array {
    pub token: Token,
    pub elements: Vec<Expr>,
}
impl Display for Array {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .elements
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<String>>()
            .join("");

        write!(f, "{}", out)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Index {
    pub token: Token,
    pub left: Box<Expr>,
    pub index: Box<Expr>,
}
impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Pair {
    pub key: Expr,
    pub value: Expr,
}
#[derive(Debug, Clone, PartialEq)]
pub struct Hash {
    pub token: Token,
    pub pairs: Vec<Pair>,
}
impl Display for Hash {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .pairs
            .iter()
            .map(|pair| format!("{}:{}", pair.key, pair.value))
            .collect::<Vec<String>>()
            .join(", ");

        write!(f, "{}", out)
    }
}
