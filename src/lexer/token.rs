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
    Macro,
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
        "macro" => Token::Macro,
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
}
