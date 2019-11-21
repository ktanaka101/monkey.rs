use crate::token;
use crate::token::{Token, TokenType};

#[derive(Debug)]
pub struct Lexer {
    input: String,
    pos: usize,
    read_pos: usize,
    ch: Option<char>,
}

impl Lexer {
    pub fn new(input: String) -> Lexer {
        let mut lexer = Lexer {
            input,
            pos: 0,
            read_pos: 0,
            ch: None,
        };

        lexer.read_char();
        lexer
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        let token = match self.ch {
            None => Token::new(TokenType::Eof, "".to_string()),
            Some(c) => match c {
                '=' => match self.peek_char() {
                    Some('=') => {
                        self.read_char();
                        Token::new(TokenType::Equal, "==".to_string())
                    }
                    _ => Token::new(TokenType::Assign, '='.to_string()),
                },
                '+' => Token::new(TokenType::Plus, '+'.to_string()),
                '-' => Token::new(TokenType::Minus, '-'.to_string()),
                '!' => match self.peek_char() {
                    Some('=') => {
                        self.read_char();
                        Token::new(TokenType::NotEqual, "!=".to_string())
                    }
                    _ => Token::new(TokenType::Bang, '!'.to_string()),
                },
                '*' => Token::new(TokenType::Asterisk, '*'.to_string()),
                '/' => Token::new(TokenType::Slash, '/'.to_string()),
                '<' => Token::new(TokenType::Lt, '<'.to_string()),
                '>' => Token::new(TokenType::Gt, '>'.to_string()),
                ',' => Token::new(TokenType::Comma, ','.to_string()),
                ';' => Token::new(TokenType::Semicolon, ';'.to_string()),
                ':' => Token::new(TokenType::Colon, ':'.to_string()),
                '(' => Token::new(TokenType::Lparen, '('.to_string()),
                ')' => Token::new(TokenType::Rparen, ')'.to_string()),
                '{' => Token::new(TokenType::Lbrace, '{'.to_string()),
                '}' => Token::new(TokenType::Rbrace, '}'.to_string()),
                '[' => Token::new(TokenType::Lbracket, '['.to_string()),
                ']' => Token::new(TokenType::Rbracket, ']'.to_string()),
                '"' => Token::new(TokenType::StringLiteral, self.read_string()),
                _ => {
                    if Self::is_letter(c) {
                        let literal = self.read_identifier();
                        return Token::new(token::lookup_ident(&literal), literal);
                    } else if Self::is_digit(c) {
                        return Token::new(TokenType::Int, self.read_number());
                    } else {
                        Token::new(TokenType::Illegal, c.to_string())
                    }
                }
            },
        };

        self.read_char();
        token
    }

    fn is_letter(ch: char) -> bool {
        ch.is_ascii_alphabetic() || ch == '_' || ch == '!' || ch == '?'
    }

    fn is_digit(ch: char) -> bool {
        ch.is_digit(10)
    }

    fn read_char(&mut self) {
        self.ch = self.peek_char();
        self.pos = self.read_pos;
        self.read_pos += 1;
    }

    fn peek_char(&self) -> Option<char> {
        if self.read_pos >= self.input.chars().count() {
            None
        } else {
            self.input.chars().nth(self.read_pos)
        }
    }

    fn read_range(&self, s: usize, e: usize) -> String {
        self.input.chars().skip(s).take(e - s).collect::<String>()
    }

    fn read_identifier(&mut self) -> String {
        let pos = self.pos;
        while let Some(c) = self.ch {
            if Self::is_letter(c) {
                self.read_char();
            } else {
                break;
            }
        }

        self.read_range(pos, self.pos)
    }

    fn read_number(&mut self) -> String {
        let pos = self.pos;
        while let Some(c) = self.ch {
            if Self::is_digit(c) {
                self.read_char();
            } else {
                break;
            }
        }

        self.read_range(pos, self.pos)
    }

    fn read_string(&mut self) -> String {
        let pos = self.pos + 1;
        loop {
            self.read_char();
            match self.ch {
                Some('"') => break,
                None => break,
                _ => (),
            }
        }
        self.read_range(pos, self.pos)
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.ch {
            if c.is_ascii_whitespace() {
                self.read_char();
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_token(token: Token, ttype: TokenType, literal: &str) {
        assert_eq!(token, Token::new(ttype, literal.to_string()));
    }

    #[test]
    fn return_tokens() {
        let input = "
            let five = 5;
            let ten = 10;

            let add = fn(x, y) {
            x + y;
            };

            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;

            if(5 < 10) {
            return true;
            } else {
            return false;
            }

            10 == 10;
            10 != 9;
            \"foobar\"
            \"foo bar\"
            [1, 2];
            {\"foo\": \"bar\"}
            ";

        let mut lexer = Lexer::new(input.to_string());

        test_token(lexer.next_token(), TokenType::Let, "let");
        test_token(lexer.next_token(), TokenType::Ident, "five");
        test_token(lexer.next_token(), TokenType::Assign, "=");
        test_token(lexer.next_token(), TokenType::Int, "5");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Let, "let");
        test_token(lexer.next_token(), TokenType::Ident, "ten");
        test_token(lexer.next_token(), TokenType::Assign, "=");
        test_token(lexer.next_token(), TokenType::Int, "10");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Let, "let");
        test_token(lexer.next_token(), TokenType::Ident, "add");
        test_token(lexer.next_token(), TokenType::Assign, "=");
        test_token(lexer.next_token(), TokenType::Function, "fn");
        test_token(lexer.next_token(), TokenType::Lparen, "(");
        test_token(lexer.next_token(), TokenType::Ident, "x");
        test_token(lexer.next_token(), TokenType::Comma, ",");
        test_token(lexer.next_token(), TokenType::Ident, "y");
        test_token(lexer.next_token(), TokenType::Rparen, ")");
        test_token(lexer.next_token(), TokenType::Lbrace, "{");
        test_token(lexer.next_token(), TokenType::Ident, "x");
        test_token(lexer.next_token(), TokenType::Plus, "+");
        test_token(lexer.next_token(), TokenType::Ident, "y");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Rbrace, "}");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Let, "let");
        test_token(lexer.next_token(), TokenType::Ident, "result");
        test_token(lexer.next_token(), TokenType::Assign, "=");
        test_token(lexer.next_token(), TokenType::Ident, "add");
        test_token(lexer.next_token(), TokenType::Lparen, "(");
        test_token(lexer.next_token(), TokenType::Ident, "five");
        test_token(lexer.next_token(), TokenType::Comma, ",");
        test_token(lexer.next_token(), TokenType::Ident, "ten");
        test_token(lexer.next_token(), TokenType::Rparen, ")");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Bang, "!");
        test_token(lexer.next_token(), TokenType::Minus, "-");
        test_token(lexer.next_token(), TokenType::Slash, "/");
        test_token(lexer.next_token(), TokenType::Asterisk, "*");
        test_token(lexer.next_token(), TokenType::Int, "5");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Int, "5");
        test_token(lexer.next_token(), TokenType::Lt, "<");
        test_token(lexer.next_token(), TokenType::Int, "10");
        test_token(lexer.next_token(), TokenType::Gt, ">");
        test_token(lexer.next_token(), TokenType::Int, "5");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::If, "if");
        test_token(lexer.next_token(), TokenType::Lparen, "(");
        test_token(lexer.next_token(), TokenType::Int, "5");
        test_token(lexer.next_token(), TokenType::Lt, "<");
        test_token(lexer.next_token(), TokenType::Int, "10");
        test_token(lexer.next_token(), TokenType::Rparen, ")");
        test_token(lexer.next_token(), TokenType::Lbrace, "{");
        test_token(lexer.next_token(), TokenType::Return, "return");
        test_token(lexer.next_token(), TokenType::True, "true");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Rbrace, "}");
        test_token(lexer.next_token(), TokenType::Else, "else");
        test_token(lexer.next_token(), TokenType::Lbrace, "{");
        test_token(lexer.next_token(), TokenType::Return, "return");
        test_token(lexer.next_token(), TokenType::False, "false");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Rbrace, "}");
        test_token(lexer.next_token(), TokenType::Int, "10");
        test_token(lexer.next_token(), TokenType::Equal, "==");
        test_token(lexer.next_token(), TokenType::Int, "10");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Int, "10");
        test_token(lexer.next_token(), TokenType::NotEqual, "!=");
        test_token(lexer.next_token(), TokenType::Int, "9");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::StringLiteral, "foobar");
        test_token(lexer.next_token(), TokenType::StringLiteral, "foo bar");
        test_token(lexer.next_token(), TokenType::Lbracket, "[");
        test_token(lexer.next_token(), TokenType::Int, "1");
        test_token(lexer.next_token(), TokenType::Comma, ",");
        test_token(lexer.next_token(), TokenType::Int, "2");
        test_token(lexer.next_token(), TokenType::Rbracket, "]");
        test_token(lexer.next_token(), TokenType::Semicolon, ";");
        test_token(lexer.next_token(), TokenType::Lbrace, "{");
        test_token(lexer.next_token(), TokenType::StringLiteral, "foo");
        test_token(lexer.next_token(), TokenType::Colon, ":");
        test_token(lexer.next_token(), TokenType::StringLiteral, "bar");
        test_token(lexer.next_token(), TokenType::Rbrace, "}");
        test_token(lexer.next_token(), TokenType::Eof, "");
    }
}
