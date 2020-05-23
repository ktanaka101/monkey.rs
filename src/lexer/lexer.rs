use super::token;
use super::token::Token;

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
            None => Token::Eof,
            Some(c) => match c {
                '=' => match self.peek_char() {
                    Some('=') => {
                        self.read_char();
                        Token::Equal
                    }
                    _ => Token::Assign,
                },
                '+' => Token::Plus,
                '-' => Token::Minus,
                '!' => match self.peek_char() {
                    Some('=') => {
                        self.read_char();
                        Token::NotEqual
                    }
                    _ => Token::Bang,
                },
                '*' => Token::Asterisk,
                '/' => Token::Slash,
                '<' => Token::Lt,
                '>' => Token::Gt,
                ',' => Token::Comma,
                ';' => Token::Semicolon,
                ':' => Token::Colon,
                '(' => Token::Lparen,
                ')' => Token::Rparen,
                '{' => Token::Lbrace,
                '}' => Token::Rbrace,
                '[' => Token::Lbracket,
                ']' => Token::Rbracket,
                '"' => Token::StringLiteral(self.read_string().into()),
                _ => {
                    if Self::is_letter(c) {
                        let literal = self.read_identifier();
                        return token::lookup_ident(&literal);
                    } else if Self::is_digit(c) {
                        return Token::Int(self.read_number());
                    } else {
                        Token::Illegal(c.to_string())
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

        assert_eq!(lexer.next_token(), Token::Let);
        assert_eq!(lexer.next_token(), Token::Ident("five".into()));
        assert_eq!(lexer.next_token(), Token::Assign);
        assert_eq!(lexer.next_token(), Token::Int("5".into()));
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Let);
        assert_eq!(lexer.next_token(), Token::Ident("ten".into()));
        assert_eq!(lexer.next_token(), Token::Assign);
        assert_eq!(lexer.next_token(), Token::Int("10".into()));
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Let);
        assert_eq!(lexer.next_token(), Token::Ident("add".into()));
        assert_eq!(lexer.next_token(), Token::Assign);
        assert_eq!(lexer.next_token(), Token::Function);
        assert_eq!(lexer.next_token(), Token::Lparen);
        assert_eq!(lexer.next_token(), Token::Ident("x".into()));
        assert_eq!(lexer.next_token(), Token::Comma);
        assert_eq!(lexer.next_token(), Token::Ident("y".into()));
        assert_eq!(lexer.next_token(), Token::Rparen);
        assert_eq!(lexer.next_token(), Token::Lbrace);
        assert_eq!(lexer.next_token(), Token::Ident("x".into()));
        assert_eq!(lexer.next_token(), Token::Plus);
        assert_eq!(lexer.next_token(), Token::Ident("y".into()));
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Rbrace);
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Let);
        assert_eq!(lexer.next_token(), Token::Ident("result".into()));
        assert_eq!(lexer.next_token(), Token::Assign);
        assert_eq!(lexer.next_token(), Token::Ident("add".into()));
        assert_eq!(lexer.next_token(), Token::Lparen);
        assert_eq!(lexer.next_token(), Token::Ident("five".into()));
        assert_eq!(lexer.next_token(), Token::Comma);
        assert_eq!(lexer.next_token(), Token::Ident("ten".into()));
        assert_eq!(lexer.next_token(), Token::Rparen);
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Bang);
        assert_eq!(lexer.next_token(), Token::Minus);
        assert_eq!(lexer.next_token(), Token::Slash);
        assert_eq!(lexer.next_token(), Token::Asterisk);
        assert_eq!(lexer.next_token(), Token::Int("5".into()));
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Int("5".into()));
        assert_eq!(lexer.next_token(), Token::Lt);
        assert_eq!(lexer.next_token(), Token::Int("10".into()));
        assert_eq!(lexer.next_token(), Token::Gt);
        assert_eq!(lexer.next_token(), Token::Int("5".into()));
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::If);
        assert_eq!(lexer.next_token(), Token::Lparen);
        assert_eq!(lexer.next_token(), Token::Int("5".into()));
        assert_eq!(lexer.next_token(), Token::Lt);
        assert_eq!(lexer.next_token(), Token::Int("10".into()));
        assert_eq!(lexer.next_token(), Token::Rparen);
        assert_eq!(lexer.next_token(), Token::Lbrace);
        assert_eq!(lexer.next_token(), Token::Return);
        assert_eq!(lexer.next_token(), Token::True);
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Rbrace);
        assert_eq!(lexer.next_token(), Token::Else);
        assert_eq!(lexer.next_token(), Token::Lbrace);
        assert_eq!(lexer.next_token(), Token::Return);
        assert_eq!(lexer.next_token(), Token::False);
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Rbrace);
        assert_eq!(lexer.next_token(), Token::Int("10".into()));
        assert_eq!(lexer.next_token(), Token::Equal);
        assert_eq!(lexer.next_token(), Token::Int("10".into()));
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Int("10".into()));
        assert_eq!(lexer.next_token(), Token::NotEqual);
        assert_eq!(lexer.next_token(), Token::Int("9".into()));
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::StringLiteral("foobar".into()),);
        assert_eq!(lexer.next_token(), Token::StringLiteral("foo bar".into()),);
        assert_eq!(lexer.next_token(), Token::Lbracket);
        assert_eq!(lexer.next_token(), Token::Int("1".into()));
        assert_eq!(lexer.next_token(), Token::Comma);
        assert_eq!(lexer.next_token(), Token::Int("2".into()));
        assert_eq!(lexer.next_token(), Token::Rbracket);
        assert_eq!(lexer.next_token(), Token::Semicolon);
        assert_eq!(lexer.next_token(), Token::Lbrace);
        assert_eq!(lexer.next_token(), Token::StringLiteral("foo".into()));
        assert_eq!(lexer.next_token(), Token::Colon);
        assert_eq!(lexer.next_token(), Token::StringLiteral("bar".into()));
        assert_eq!(lexer.next_token(), Token::Rbrace);
        assert_eq!(lexer.next_token(), Token::Eof);
    }
}
