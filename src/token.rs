#[derive(Clone, PartialEq, Debug)]
pub enum TokenType {
    Illegal,
    Eof,
    // identifier, literal
    Ident,
    Int,
    StringLiteral,
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

pub fn lookup_ident(ident: &str) -> TokenType {
    match ident {
        "fn" => TokenType::Function,
        "let" => TokenType::Let,
        "true" => TokenType::True,
        "false" => TokenType::False,
        "if" => TokenType::If,
        "else" => TokenType::Else,
        "return" => TokenType::Return,
        _ => TokenType::Ident,
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Token {
    pub token_t: TokenType,
    pub literal: String,
}

impl Token {
    pub fn new(token_t: TokenType, literal: String) -> Token {
        Token { token_t, literal }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_return_token() {
        assert_eq!(lookup_ident("fn"), TokenType::Function);
        assert_eq!(lookup_ident("let"), TokenType::Let);
        assert_eq!(lookup_ident("true"), TokenType::True);
        assert_eq!(lookup_ident("false"), TokenType::False);
        assert_eq!(lookup_ident("if"), TokenType::If);
        assert_eq!(lookup_ident("else"), TokenType::Else);
        assert_eq!(lookup_ident("return"), TokenType::Return);
        assert_eq!(lookup_ident("fna"), TokenType::Ident);
    }
}
