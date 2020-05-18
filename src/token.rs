#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    Illegal(String),
    Eof,
    // identifier, literal
    Ident(String),
    Int(String),
    StringLiteral(String),
    // operator
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
    // delimiter
    Comma,
    Semicolon,
    Colon,
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
    Lbracket,
    Rbracket,
    // keyword
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

impl Token {
    pub fn literal(&self) -> &str {
        match self {
            Self::Illegal(s) | Self::Ident(s) | Self::Int(s) | Self::StringLiteral(s) => s,
            Self::Eof => "",
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
            Self::Comma => ",",
            Self::Semicolon => ";",
            Self::Colon => ":",
            Self::Lparen => "(",
            Self::Rparen => ")",
            Self::Lbrace => "{",
            Self::Rbrace => "}",
            Self::Lbracket => "[",
            Self::Rbracket => "]",
            Self::Function => "fn",
            Self::Let => "let",
            Self::True => "true",
            Self::False => "false",
            Self::If => "if",
            Self::Else => "else",
            Self::Return => "return",
        }
    }
}

pub fn lookup_ident(ident: &str) -> Token {
    match ident {
        "fn" => Token::Function,
        "let" => Token::Let,
        "true" => Token::True,
        "false" => Token::False,
        "if" => Token::If,
        "else" => Token::Else,
        "return" => Token::Return,
        id => Token::Ident(id.into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_return_token() {
        assert_eq!(lookup_ident("fn"), Token::Function);
        assert_eq!(lookup_ident("let"), Token::Let);
        assert_eq!(lookup_ident("true"), Token::True);
        assert_eq!(lookup_ident("false"), Token::False);
        assert_eq!(lookup_ident("if"), Token::If);
        assert_eq!(lookup_ident("else"), Token::Else);
        assert_eq!(lookup_ident("return"), Token::Return);
        assert_eq!(lookup_ident("fna"), Token::Ident("fna".into()));
    }

    #[test]
    fn literal() {
        assert_eq!(Token::Illegal("abc".into()).literal(), "abc");
        assert_eq!(Token::Illegal("def".into()).literal(), "def");

        assert_eq!(Token::Ident("abc".into()).literal(), "abc");
        assert_eq!(Token::Ident("def".into()).literal(), "def");

        assert_eq!(Token::Int("abc".into()).literal(), "abc");
        assert_eq!(Token::Int("def".into()).literal(), "def");

        assert_eq!(Token::StringLiteral("abc".into()).literal(), "abc");
        assert_eq!(Token::StringLiteral("def".into()).literal(), "def");

        assert_eq!(Token::Eof.literal(), "");
        assert_eq!(Token::Assign.literal(), "=");
        assert_eq!(Token::Plus.literal(), "+");
        assert_eq!(Token::Minus.literal(), "-");
        assert_eq!(Token::Bang.literal(), "!");
        assert_eq!(Token::Asterisk.literal(), "*");
        assert_eq!(Token::Slash.literal(), "/");
        assert_eq!(Token::Equal.literal(), "==");
        assert_eq!(Token::NotEqual.literal(), "!=");
        assert_eq!(Token::Lt.literal(), "<");
        assert_eq!(Token::Gt.literal(), ">");
        assert_eq!(Token::Comma.literal(), ",");
        assert_eq!(Token::Semicolon.literal(), ";");
        assert_eq!(Token::Colon.literal(), ":");
        assert_eq!(Token::Lparen.literal(), "(");
        assert_eq!(Token::Rparen.literal(), ")");
        assert_eq!(Token::Lbrace.literal(), "{");
        assert_eq!(Token::Rbrace.literal(), "}");
        assert_eq!(Token::Lbracket.literal(), "[");
        assert_eq!(Token::Rbracket.literal(), "]");
        assert_eq!(Token::Function.literal(), "fn");
        assert_eq!(Token::Let.literal(), "let");
        assert_eq!(Token::True.literal(), "true");
        assert_eq!(Token::False.literal(), "false");
        assert_eq!(Token::If.literal(), "if");
        assert_eq!(Token::Else.literal(), "else");
        assert_eq!(Token::Return.literal(), "return");
    }
}
