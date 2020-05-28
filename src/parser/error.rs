use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Expect operator. {0}")]
    ExpectOperator(String),
    #[error("Expect token. {0}")]
    ExpectExpression(String),
    #[error("Expect identifier token. {0}")]
    ExpectIdentifier(String),
    #[error("Invlaid token. {0}")]
    InvalidPrefix(String),
    #[error("Expect token. {0}")]
    InvalidInfix(String),
    #[error("Expect peek {0}. Received {1}.")]
    ExpectPeek(String, String),
    #[error("Expect peek `}}` or `,`. {0}")]
    InvalidHashLiteral(String),
    #[error("Expect StringLiteral token. {0}")]
    InvalidStringLiteral(String),
    #[error("Expect Identifier token. {0}")]
    InvalidFunctionParam(String),
    #[error("Expect boolean token. {0}")]
    InvalidBooleanLiteral(String),
    #[error("Expect integer token. {0}")]
    InvalidIntegerLiteral(String),
    #[error("Integer parse error. {0}")]
    InvalidInteger(String),
}
