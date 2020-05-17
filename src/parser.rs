use crate::ast;
use crate::ast::{Expr, Stmt};
use crate::error::{MonkeyError, Result};
use crate::lexer::Lexer;
use crate::token::Token;

#[derive(PartialOrd, PartialEq, Debug)]
enum Priority {
    Lowest,
    Equals,
    Lessgreater,
    Sum,
    Product,
    Prefix,
    Call,
    Index,
}

impl From<&Token> for Priority {
    fn from(value: &Token) -> Priority {
        match value {
            Token::Equal => Priority::Equals,
            Token::NotEqual => Priority::Equals,
            Token::Lt => Priority::Lessgreater,
            Token::Gt => Priority::Lessgreater,
            Token::Plus => Priority::Sum,
            Token::Minus => Priority::Sum,
            Token::Slash => Priority::Product,
            Token::Asterisk => Priority::Product,
            Token::Lparen => Priority::Call,
            Token::Lbracket => Priority::Index,
            _ => Priority::Lowest,
        }
    }
}

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    cur_token: Token,
    peek_token: Token,
    pub errors: Vec<String>,
}

fn parse_error<T>(err: &str) -> Result<T> {
    Err(MonkeyError::Parser(err.to_string()))
}

#[derive(Debug)]
enum InfixFn {
    Infix,
    Call,
    Index,
}

fn token_to_operator(t: &Token) -> Result<ast::Operator> {
    Ok(match t {
        Token::Assign => ast::Operator::Assign,
        Token::Plus => ast::Operator::Plus,
        Token::Minus => ast::Operator::Minus,
        Token::Bang => ast::Operator::Bang,
        Token::Asterisk => ast::Operator::Asterisk,
        Token::Slash => ast::Operator::Slash,
        Token::Equal => ast::Operator::Equal,
        Token::NotEqual => ast::Operator::NotEqual,
        Token::Lt => ast::Operator::Lt,
        Token::Gt => ast::Operator::Gt,
        t => return parse_error(&format!("Expect oeprator. {:?}", t)),
    })
}

impl Parser {
    pub fn new(mut lexer: Lexer) -> Parser {
        Parser {
            cur_token: lexer.next_token(),
            peek_token: lexer.next_token(),
            lexer,
            errors: Vec::new(),
        }
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token();
    }

    pub fn parse_program(&mut self) -> Result<ast::Program> {
        let mut program = ast::Program::default();

        while self.cur_token != Token::Eof {
            let stmt = self.parse_statement()?;
            program.statements.push(stmt);
            self.next_token();
        }

        Ok(program)
    }

    fn parse_statement(&mut self) -> Result<Stmt> {
        Ok(match self.cur_token {
            Token::Let => Stmt::Let(self.parse_let_statement()?),
            Token::Return => Stmt::Return(self.parse_return_statement()?),
            _ => Stmt::ExprStmt(self.parse_expr_statement()?),
        })
    }

    fn parse_let_statement(&mut self) -> Result<ast::Let> {
        let token = self.cur_token.clone();
        self.expect_peek(Token::Ident("_".to_string()))?;

        let name = ast::Identifier {
            token: self.cur_token.clone(),
            value: match &self.cur_token {
                Token::Ident(id) => id.clone(),
                _ => unreachable!(),
            },
        };

        self.expect_peek(Token::Assign)?;

        self.next_token();
        let value = self.parse_expr(Priority::Lowest)?;
        if self.peek_token_is(Token::Semicolon) {
            self.next_token();
        }

        Ok(ast::Let { token, name, value })
    }

    fn parse_return_statement(&mut self) -> Result<ast::Return> {
        let token = self.cur_token.clone();

        self.next_token();

        let return_value = self.parse_expr(Priority::Lowest)?;

        if self.peek_token_is(Token::Semicolon) {
            self.next_token();
        };

        Ok(ast::Return {
            token,
            return_value,
        })
    }

    fn parse_expr_statement(&mut self) -> Result<ast::ExprStmt> {
        let token = self.cur_token.clone();
        let expr = self.parse_expr(Priority::Lowest)?;

        if self.peek_token_is(Token::Semicolon) {
            self.next_token();
        }

        Ok(ast::ExprStmt { token, expr })
    }

    fn parse_expr(&mut self, precedende: Priority) -> Result<Expr> {
        match &self.cur_token {
            t @ Token::Illegal(_)
            | t @ Token::Eof
            | t @ Token::Assign
            | t @ Token::Plus
            | t @ Token::Asterisk
            | t @ Token::Slash
            | t @ Token::Equal
            | t @ Token::NotEqual
            | t @ Token::Lt
            | t @ Token::Gt
            | t @ Token::Comma
            | t @ Token::Semicolon
            | t @ Token::Colon
            | t @ Token::Rparen
            | t @ Token::Rbrace
            | t @ Token::Rbracket
            | t @ Token::Let
            | t @ Token::Else
            | t @ Token::Return => return parse_error(&format!("Invalid token. {:?}", t)),
            Token::Ident(_)
            | Token::Int(_)
            | Token::Bang
            | Token::Minus
            | Token::True
            | Token::False
            | Token::Lparen
            | Token::If
            | Token::Function
            | Token::StringLiteral(_)
            | Token::Lbracket
            | Token::Lbrace => (),
        }

        let mut left_expr = self.prefix_parse_fns(self.cur_token.clone())?;

        while !self.peek_token_is(Token::Semicolon) && precedende < Priority::from(&self.peek_token)
        {
            let infix_fn = self.infix_parse_fns(self.peek_token.clone())?;

            self.next_token();

            left_expr = match infix_fn {
                InfixFn::Infix => Expr::InfixExpr(self.parse_infix_expr(left_expr)?),
                InfixFn::Call => Expr::Call(self.parse_call_expr(left_expr)?),
                InfixFn::Index => Expr::Index(self.parse_index_expr(left_expr)?),
            };
        }

        Ok(left_expr)
    }

    fn parse_identifier(&self) -> Result<ast::Identifier> {
        Ok(ast::Identifier {
            token: self.cur_token.clone(),
            value: match &self.cur_token {
                Token::Ident(val) => val.clone(),
                t => parse_error(&format!("Expect identifier token. {:?}", t))?,
            },
        })
    }

    fn parse_integer_literal(&self) -> Result<ast::Integer> {
        let value = match &self.cur_token {
            Token::Int(val) => val
                .parse::<i64>()
                .or_else(|e| parse_error(&format!("Integer parse error. {}", e)))?,
            t => parse_error(&format!("Expect integer token. {:?}", t))?,
        };

        Ok(ast::Integer {
            token: self.cur_token.clone(),
            value,
        })
    }

    fn parse_bool_literal(&self) -> Result<ast::Boolean> {
        match &self.cur_token {
            Token::True => Ok(ast::Boolean {
                token: self.cur_token.clone(),
                value: true,
            }),
            Token::False => Ok(ast::Boolean {
                token: self.cur_token.clone(),
                value: false,
            }),
            t => parse_error(&format!("Expect boolean token. {:?}", t)),
        }
    }

    fn parse_grouped_expr(&mut self) -> Result<Expr> {
        self.next_token();
        self.parse_expr(Priority::Lowest)
    }

    fn parse_prefix_expr(&mut self) -> Result<ast::PrefixExpr> {
        let token = self.cur_token.clone();
        let ope = token_to_operator(&self.cur_token)?;
        self.next_token();
        let right = Box::new(self.parse_expr(Priority::Prefix)?);

        Ok(ast::PrefixExpr { token, ope, right })
    }

    fn parse_infix_expr(&mut self, left: Expr) -> Result<ast::InfixExpr> {
        let token = self.cur_token.clone();
        let ope = token_to_operator(&self.cur_token)?;
        let pre = Priority::from(&self.cur_token);

        self.next_token();

        let right = Box::new(self.parse_expr(pre)?);

        Ok(ast::InfixExpr {
            token,
            left: Box::new(left),
            ope,
            right,
        })
    }

    fn parse_if_expr(&mut self) -> Result<ast::If> {
        let token = self.cur_token.clone();
        self.expect_peek(Token::Lparen)?;

        self.next_token();

        let cond = Box::new(self.parse_expr(Priority::Lowest)?);

        self.expect_peek(Token::Rparen)?;
        self.expect_peek(Token::Lbrace)?;

        let consequence = self.parse_block_statement()?;

        let alternative = if self.peek_token_is(Token::Else) {
            self.next_token();
            self.expect_peek(Token::Lbrace)?;

            Some(self.parse_block_statement()?)
        } else {
            None
        };

        Ok(ast::If {
            token,
            cond,
            consequence,
            alternative,
        })
    }

    fn parse_block_statement(&mut self) -> Result<ast::Block> {
        let token = self.cur_token.clone();
        let mut statements = Vec::<Stmt>::new();

        self.next_token();

        while !(self.cur_token_is(Token::Rbrace) || self.cur_token_is(Token::Eof)) {
            statements.push(self.parse_statement()?);
            self.next_token();
        }

        Ok(ast::Block { token, statements })
    }

    fn parse_function_literal(&mut self) -> Result<ast::Function> {
        let token = self.cur_token.clone();
        self.expect_peek(Token::Lparen)?;

        let params = self.parse_function_params()?;
        self.expect_peek(Token::Lbrace)?;

        let body = self.parse_block_statement()?;

        Ok(ast::Function {
            token,
            params,
            body,
        })
    }

    fn parse_function_params(&mut self) -> Result<Vec<ast::Identifier>> {
        let mut identifiers = Vec::<ast::Identifier>::new();

        if self.peek_token_is(Token::Rparen) {
            self.next_token();
            return Ok(identifiers);
        }

        self.next_token();

        identifiers.push(ast::Identifier {
            token: self.cur_token.clone(),
            value: match &self.cur_token {
                Token::Ident(t) => t.clone(),
                t => parse_error(&format!("Expect Identifier token. {:?}", t))?,
            },
        });

        while self.peek_token_is(Token::Comma) {
            self.next_token();
            self.next_token();
            identifiers.push(ast::Identifier {
                token: self.cur_token.clone(),
                value: match &self.cur_token {
                    Token::Ident(t) => t.clone(),
                    t => parse_error(&format!("Expect Identifier token. {:?}", t))?,
                },
            })
        }
        self.expect_peek(Token::Rparen)?;

        Ok(identifiers)
    }

    fn parse_call_expr(&mut self, func: Expr) -> Result<ast::Call> {
        Ok(ast::Call {
            token: self.cur_token.clone(),
            func: Box::new(func),
            args: self.parse_expr_list(Token::Rparen)?,
        })
    }

    fn parse_expr_list(&mut self, end_token_t: Token) -> Result<Vec<Expr>> {
        let mut expr_list = Vec::<Expr>::new();

        if self.peek_token_is(end_token_t.clone()) {
            self.next_token();
            return Ok(expr_list);
        }

        self.next_token();
        expr_list.push(self.parse_expr(Priority::Lowest)?);

        while self.peek_token_is(Token::Comma) {
            self.next_token();
            self.next_token();
            expr_list.push(self.parse_expr(Priority::Lowest)?);
        }

        self.expect_peek(end_token_t)?;

        Ok(expr_list)
    }

    fn parse_string_literal(&self) -> Result<ast::StringLit> {
        Ok(ast::StringLit {
            token: self.cur_token.clone(),
            value: match &self.cur_token {
                Token::StringLiteral(s) => s.clone(),
                t => parse_error(&format!("Expect StringLiteral token. {:?}", t))?,
            },
        })
    }

    fn parse_array_literal(&mut self) -> Result<ast::Array> {
        Ok(ast::Array {
            token: self.cur_token.clone(),
            elements: self.parse_expr_list(Token::Rbracket)?,
        })
    }

    fn parse_index_expr(&mut self, left: Expr) -> Result<ast::Index> {
        let token = self.cur_token.clone();
        self.next_token();
        let index = self.parse_expr(Priority::Lowest)?;
        self.expect_peek(Token::Rbracket)?;

        Ok(ast::Index {
            token,
            left: Box::new(left),
            index: Box::new(index),
        })
    }

    fn parse_hash_literal(&mut self) -> Result<ast::Hash> {
        let token = self.cur_token.clone();
        let mut pairs = Vec::<ast::Pair>::new();

        while !self.peek_token_is(Token::Rbrace) {
            self.next_token();
            let key = self.parse_expr(Priority::Lowest)?;
            self.expect_peek(Token::Colon)?;
            self.next_token();
            let value = self.parse_expr(Priority::Lowest)?;
            pairs.push(ast::Pair { key, value });

            if !self.peek_token_is(Token::Rbrace) && self.expect_peek(Token::Comma).is_err() {
                return parse_error(&format!("Expect `}}` or `,`. {:?}", &self.cur_token));
            }
        }
        self.expect_peek(Token::Rbrace)?;

        Ok(ast::Hash { token, pairs })
    }

    fn cur_token_is(&self, token_t: Token) -> bool {
        match token_t {
            Token::Illegal(_) => match self.cur_token {
                Token::Illegal(_) => true,
                _ => false,
            },
            Token::Ident(_) => match self.cur_token {
                Token::Ident(_) => true,
                _ => false,
            },
            Token::Int(_) => match self.cur_token {
                Token::Int(_) => true,
                _ => false,
            },
            Token::StringLiteral(_) => match self.cur_token {
                Token::StringLiteral(_) => true,
                _ => false,
            },
            t => self.cur_token == t,
        }
    }

    fn peek_token_is(&self, token_t: Token) -> bool {
        match token_t {
            Token::Illegal(_) => match self.peek_token {
                Token::Illegal(_) => true,
                _ => false,
            },
            Token::Ident(_) => match self.peek_token {
                Token::Ident(_) => true,
                _ => false,
            },
            Token::Int(_) => match self.peek_token {
                Token::Int(_) => true,
                _ => false,
            },
            Token::StringLiteral(_) => match self.peek_token {
                Token::StringLiteral(_) => true,
                _ => false,
            },
            t => self.peek_token == t,
        }
    }

    fn expect_peek(&mut self, token_t: Token) -> Result<()> {
        if self.peek_token_is(token_t.clone()) {
            self.next_token();
            Ok(())
        } else {
            parse_error(&format!(
                "Expect peek {:?}. Received {:?}.",
                &self.peek_token, &token_t
            ))
        }
    }

    fn prefix_parse_fns(&mut self, token_t: Token) -> Result<Expr> {
        Ok(match token_t {
            Token::Ident(_) => Expr::Identifier(self.parse_identifier()?),
            Token::Int(_) => Expr::Integer(self.parse_integer_literal()?),
            Token::Bang | Token::Minus => Expr::PrefixExpr(self.parse_prefix_expr()?),
            Token::True | Token::False => Expr::Boolean(self.parse_bool_literal()?),
            Token::Lparen => self.parse_grouped_expr()?,
            Token::If => Expr::If(self.parse_if_expr()?),
            Token::Function => Expr::Function(self.parse_function_literal()?),
            Token::StringLiteral(_) => Expr::StringLit(self.parse_string_literal()?),
            Token::Lbracket => Expr::Array(self.parse_array_literal()?),
            Token::Lbrace => Expr::Hash(self.parse_hash_literal()?),
            t => return parse_error(&format!("Invalid token. {:?}", t)),
        })
    }

    fn infix_parse_fns(&self, token_t: Token) -> Result<InfixFn> {
        Ok(match token_t {
            Token::Plus
            | Token::Minus
            | Token::Slash
            | Token::Asterisk
            | Token::Equal
            | Token::NotEqual
            | Token::Lt
            | Token::Gt => InfixFn::Infix,
            Token::Lparen => InfixFn::Call,
            Token::Lbracket => InfixFn::Index,
            t => return parse_error(&format!("Invalid token. {:?}", t)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Id<'a>(&'a str);
    enum Val<'a> {
        S(&'a str),
        B(bool),
        Id(Id<'a>),
        I(i64),
        Infix(Box<Val<'a>>, &'a str, Box<Val<'a>>),
    }

    #[test]
    fn test_let_stmts() {
        let inputs = vec![
            ("let x = 5", Id("x"), Val::I(5)),
            ("let x = 5;", Id("x"), Val::I(5)),
            ("let y = true;", Id("y"), Val::B(true)),
            ("let foobar = y;", Id("foobar"), Val::Id(Id("y"))),
        ];

        for (input, id, v) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);
            test_let_by_stmt(&program.statements[0], &id, &v);
        }
    }

    #[test]
    fn test_return_stmts() {
        let inputs = vec![
            ("return 5", Val::I(5)),
            ("return 5;", Val::I(5)),
            ("return true;", Val::B(true)),
            ("return y;", Val::Id(Id("y"))),
        ];

        for (input, v) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);
            test_return_by_stmt(&program.statements[0], &v);
        }
    }

    #[test]
    fn test_identifier_exprs() {
        let input = "foobar";
        let program = test_parse(input);
        assert_eq!(program.statements.len(), 1);
        test_identifier_by_stmt(&program.statements[0], "foobar");
    }

    #[test]
    fn test_integer_exprs() {
        let inputs = vec![("5", 5), ("5;", 5)];

        for (input, v) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);
            test_interger_by_stmt(&program.statements[0], v);
        }
    }

    #[test]
    fn test_boolean_exprs() {
        let inputs = vec![("true", true), ("true;", true), ("false;", false)];

        for (input, v) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);
            test_boolean_by_stmt(&program.statements[0], v);
        }
    }

    #[test]
    fn test_prefix_exprs() {
        let inputs = vec![
            ("!5", "!", Val::I(5)),
            ("!5;", "!", Val::I(5)),
            ("-15;", "-", Val::I(15)),
            ("!true;", "!", Val::B(true)),
            ("!false;", "!", Val::B(false)),
        ];

        for (input, ope, v) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);
            test_prefix_by_stmt(&program.statements[0], ope, &v);
        }
    }

    #[test]
    fn test_infix_exprs() {
        let inputs = vec![
            ("5 + 5", Val::I(5), "+", Val::I(5)),
            ("5 + 5;", Val::I(5), "+", Val::I(5)),
            ("5 - 5;", Val::I(5), "-", Val::I(5)),
            ("5 * 5;", Val::I(5), "*", Val::I(5)),
            ("5 / 5;", Val::I(5), "/", Val::I(5)),
            ("5 > 5;", Val::I(5), ">", Val::I(5)),
            ("5 < 5;", Val::I(5), "<", Val::I(5)),
            ("5 == 5;", Val::I(5), "==", Val::I(5)),
            ("5 != 5;", Val::I(5), "!=", Val::I(5)),
            ("true == true;", Val::B(true), "==", Val::B(true)),
            ("true != false;", Val::B(true), "!=", Val::B(false)),
            ("false == false;", Val::B(false), "==", Val::B(false)),
        ];

        for (input, left, ope, right) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);
            test_infix_by_stmt(&program.statements[0], &left, &ope, &right);
        }
    }

    #[test]
    fn test_if_exprs() {
        let input = "if (x < y) { x }";

        let program = test_parse(input);
        assert_eq!(program.statements.len(), 1);

        let expr_stmt = if let Stmt::ExprStmt(x) = &program.statements[0] {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt");
        };
        assert_eq!(expr_stmt.token, Token::If);

        let if_expr = if let Expr::If(x) = &expr_stmt.expr {
            x
        } else {
            panic!("Expect type is Expr::If");
        };

        assert_eq!(if_expr.token, Token::If);

        test_infix_by_expr(
            if_expr.cond.as_ref(),
            &Val::Id(Id("x")),
            "<",
            &Val::Id(Id("y")),
        );

        assert_eq!(if_expr.consequence.token, Token::Lbrace);
        assert_eq!(if_expr.consequence.statements.len(), 1);
        test_identifier_by_stmt(&if_expr.consequence.statements[0], "x");
        assert_eq!(if_expr.alternative, None);
    }

    #[test]
    fn test_if_else_exprs() {
        let inputs = vec![
            "if (x < y) { x } else { y }",
            "if (x < y) { x; } else { y; }",
        ];

        for input in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);

            let expr_stmt = if let Stmt::ExprStmt(x) = &program.statements[0] {
                x
            } else {
                panic!("Expect type is Stmt::ExprStmt");
            };
            assert_eq!(expr_stmt.token, Token::If);

            let if_expr = if let Expr::If(x) = &expr_stmt.expr {
                x
            } else {
                panic!("Expect type is Expr::If");
            };

            assert_eq!(if_expr.token, Token::If);

            test_infix_by_expr(
                if_expr.cond.as_ref(),
                &Val::Id(Id("x")),
                "<",
                &Val::Id(Id("y")),
            );

            assert_eq!(if_expr.consequence.token, Token::Lbrace);
            assert_eq!(if_expr.consequence.statements.len(), 1);
            test_identifier_by_stmt(&if_expr.consequence.statements[0], "x");

            let alt = if let Some(x) = &if_expr.alternative {
                x
            } else {
                panic!("Expect some Expr::Block");
            };
            assert_eq!(alt.token, Token::Lbrace);
            assert_eq!(alt.statements.len(), 1);
            test_identifier_by_stmt(&alt.statements[0], "y");
        }
    }

    #[test]
    fn test_function_exprs() {
        let inputs = vec!["fn(x, y) { x + y }", "fn(x, y) { x + y; }"];

        for input in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);

            let expr_stmt = if let Stmt::ExprStmt(x) = &program.statements[0] {
                x
            } else {
                panic!("Expect type is Stmt::ExprStmt");
            };

            assert_eq!(expr_stmt.token, Token::Function);

            let fn_expr = if let Expr::Function(x) = &expr_stmt.expr {
                x
            } else {
                panic!("Expect type is Expr::Function")
            };

            assert_eq!(fn_expr.token, Token::Function);
            assert_eq!(fn_expr.params.len(), 2);
            test_identifier(&fn_expr.params[0], "x");
            test_identifier(&fn_expr.params[1], "y");

            assert_eq!(fn_expr.body.token, Token::Lbrace);
            assert_eq!(fn_expr.body.statements.len(), 1);
            test_infix_by_stmt(
                &fn_expr.body.statements[0],
                &Val::Id(Id("x")),
                "+",
                &Val::Id(Id("y")),
            )
        }
    }

    #[test]
    fn test_function_params() {
        let inputs = vec![
            ("fn() {};", vec![]),
            ("fn(x) {};", vec!["x"]),
            ("fn(x, y, z) {};", vec!["x", "y", "z"]),
        ];

        for (input, ids) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);

            let stmt_expr = if let Stmt::ExprStmt(x) = &program.statements[0] {
                x
            } else {
                panic!("Expect type is Stmt::ExprStmt.");
            };
            assert_eq!(stmt_expr.token, Token::Function);

            let fn_expr = if let Expr::Function(x) = &stmt_expr.expr {
                x
            } else {
                panic!("Expect type is Expr::Function.");
            };
            assert_eq!(fn_expr.token, Token::Function);
            assert_eq!(fn_expr.params.len(), ids.len());

            for (i, id) in ids.into_iter().enumerate() {
                test_identifier(&fn_expr.params[i], id);
            }
        }
    }

    #[test]
    fn test_call_exprs() {
        let input = "add(1, 2 * 3, 4 + 5);";
        let program = test_parse(input);
        assert_eq!(program.statements.len(), 1);

        let stmt_expr = if let Stmt::ExprStmt(x) = &program.statements[0] {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt");
        };
        assert_eq!(stmt_expr.token, Token::Ident("add".into()));

        let call_expr = if let Expr::Call(x) = &stmt_expr.expr {
            x
        } else {
            panic!("Expect type is Expr::Call");
        };
        assert_eq!(call_expr.token, Token::Lparen);

        test_expr(call_expr.func.as_ref(), &Val::Id(Id("add")));
        assert_eq!(call_expr.args.len(), 3);
        test_expr(&call_expr.args[0], &Val::I(1));
        test_infix_by_expr(&call_expr.args[1], &Val::I(2), "*", &Val::I(3));
        test_infix_by_expr(&call_expr.args[2], &Val::I(4), "+", &Val::I(5));
    }

    #[test]
    fn test_string_exprs() {
        let input = "\"hello world\"";
        let program = test_parse(input);
        assert_eq!(program.statements.len(), 1);

        let stmt_expr = if let Stmt::ExprStmt(x) = &program.statements[0] {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt.");
        };
        assert_eq!(stmt_expr.token, Token::StringLiteral("hello world".into()));

        test_expr(&stmt_expr.expr, &Val::S("hello world"));
    }

    #[test]
    fn test_array_expr() {
        let input = "[1, 2 * 2, 3 + 3]";
        let program = test_parse(input);
        assert_eq!(program.statements.len(), 1);

        let stmt_expr = if let Stmt::ExprStmt(x) = &program.statements[0] {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt.");
        };
        assert_eq!(stmt_expr.token, Token::Lbracket);

        let array_expr = if let Expr::Array(x) = &stmt_expr.expr {
            x
        } else {
            panic!("Expect type is Expr::Array.");
        };
        assert_eq!(array_expr.token, Token::Lbracket);
        assert_eq!(array_expr.elements.len(), 3);
        test_expr(&array_expr.elements[0], &Val::I(1));
        test_infix_by_expr(&array_expr.elements[1], &Val::I(2), "*", &Val::I(2));
        test_infix_by_expr(&array_expr.elements[2], &Val::I(3), "+", &Val::I(3));
    }

    #[test]
    fn test_index_expr() {
        let input = "myArray[1 + 1]";
        let program = test_parse(input);
        assert_eq!(program.statements.len(), 1);

        let stmt_expr = if let Stmt::ExprStmt(x) = &program.statements[0] {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt.");
        };
        assert_eq!(stmt_expr.token, Token::Ident("myArray".into()));

        let index_expr = if let Expr::Index(x) = &stmt_expr.expr {
            x
        } else {
            panic!("Expect type is Expr::Index.");
        };
        assert_eq!(index_expr.token, Token::Lbracket);
        test_expr(index_expr.left.as_ref(), &Val::Id(Id("myArray")));
        test_infix_by_expr(index_expr.index.as_ref(), &Val::I(1), "+", &Val::I(1));
    }

    #[test]
    fn test_hash_expr() {
        let inputs = vec![
            ("{}", vec![]),
            (
                r#"{"one": 1, "two": 2, "three": 3}"#,
                vec![
                    (Val::S("one"), Val::I(1)),
                    (Val::S("two"), Val::I(2)),
                    (Val::S("three"), Val::I(3)),
                ],
            ),
            (
                r#"{"one": 0 + 1, "two": 10 - 8, "three": 15 / 5}"#,
                vec![
                    (
                        Val::S("one"),
                        Val::Infix(Box::new(Val::I(0)), "+", Box::new(Val::I(1))),
                    ),
                    (
                        Val::S("two"),
                        Val::Infix(Box::new(Val::I(10)), "-", Box::new(Val::I(8))),
                    ),
                    (
                        Val::S("three"),
                        Val::Infix(Box::new(Val::I(15)), "/", Box::new(Val::I(5))),
                    ),
                ],
            ),
            (
                r#"{1: 111, 2: "b", 3: true}"#,
                vec![
                    (Val::I(1), Val::I(111)),
                    (Val::I(2), Val::S("b")),
                    (Val::I(3), Val::B(true)),
                ],
            ),
            (
                r#"{true: 1, false: "abc"}"#,
                vec![(Val::B(true), Val::I(1)), (Val::B(false), Val::S("abc"))],
            ),
        ];

        for (input, expect_list) in inputs.into_iter() {
            let program = test_parse(input);
            assert_eq!(program.statements.len(), 1);

            let expr_stmt = if let Stmt::ExprStmt(x) = &program.statements[0] {
                x
            } else {
                panic!("Expect type is Stmt::ExprStmt.");
            };
            assert_eq!(expr_stmt.token, Token::Lbrace);

            let hash_expr = if let Expr::Hash(x) = &expr_stmt.expr {
                x
            } else {
                panic!("Expect type is Expr::Hash.");
            };
            assert_eq!(hash_expr.token, Token::Lbrace);
            assert_eq!(hash_expr.pairs.len(), expect_list.len());
            for (i, expect) in expect_list.into_iter().enumerate() {
                test_expr(&hash_expr.pairs[i].key, &expect.0);
                test_expr(&hash_expr.pairs[i].value, &expect.1);
            }
        }
    }

    fn test_infix_by_expr(expr: &Expr, l: &Val, o: &str, r: &Val) {
        let infix = if let Expr::InfixExpr(x) = &expr {
            x
        } else {
            panic!("Expect type is Expr::InfixExpr.");
        };

        test_infix(&infix, l, o, r);
    }

    fn test_infix_by_stmt(stmt: &Stmt, l: &Val, o: &str, r: &Val) {
        let expr_stmt = if let Stmt::ExprStmt(x) = stmt {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt");
        };

        assert_eq!(
            expr_stmt.token,
            match l {
                Val::I(v) => Token::Int(v.to_string()),
                Val::B(b) => {
                    if *b {
                        Token::True
                    } else {
                        Token::False
                    }
                }
                Val::Id(id) => Token::Ident(id.0.into()),
                _ => panic!("Invalid Val."),
            }
        );

        let infix = if let Expr::InfixExpr(x) = &expr_stmt.expr {
            x
        } else {
            panic!("Expect type is Expr::InfixExpr");
        };

        test_infix(&infix, &l, &o, &r);
    }

    fn test_infix(infix: &ast::InfixExpr, l: &Val, o: &str, r: &Val) {
        assert_eq!(
            infix.token,
            match o {
                "+" => Token::Plus,
                "-" => Token::Minus,
                "/" => Token::Slash,
                "*" => Token::Asterisk,
                "==" => Token::Equal,
                "!=" => Token::NotEqual,
                "<" => Token::Lt,
                ">" => Token::Gt,
                _ => panic!("Invalid token."),
            },
        );

        test_expr(&infix.left, l);
        test_expr(&infix.right, r);
        test_operator(&infix.ope, o);
    }

    fn test_prefix_by_stmt(stmt: &Stmt, ope: &str, r: &Val) {
        let expr_stmt = if let Stmt::ExprStmt(x) = stmt {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt");
        };

        assert_eq!(
            expr_stmt.token,
            match ope {
                "!" => Token::Bang,
                "-" => Token::Minus,
                _ => panic!("Expect operator is '!' or '-'"),
            }
        );

        let prefix_expr = if let Expr::PrefixExpr(x) = &expr_stmt.expr {
            x
        } else {
            panic!("Expect type is Expr::PrefixExpr");
        };
        assert_eq!(
            prefix_expr.token,
            match ope {
                "!" => Token::Bang,
                "-" => Token::Minus,
                _ => panic!("Expect operator is '!' or '-'"),
            },
        );
        test_operator(&prefix_expr.ope, ope);
        test_expr(&prefix_expr.right, &r);
    }

    fn test_operator(ope: &ast::Operator, ope_s: &str) {
        assert_eq!(
            match ope {
                ast::Operator::Assign => "=",
                ast::Operator::Asterisk => "*",
                ast::Operator::Bang => "!",
                ast::Operator::Equal => "==",
                ast::Operator::Gt => ">",
                ast::Operator::Lt => "<",
                ast::Operator::Minus => "-",
                ast::Operator::NotEqual => "!=",
                ast::Operator::Plus => "+",
                ast::Operator::Slash => "/",
            },
            ope_s,
        );
    }

    fn test_boolean_by_stmt(stmt: &Stmt, v: bool) {
        let expr_stmt = if let Stmt::ExprStmt(x) = stmt {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt");
        };

        let expected_token = if v { Token::True } else { Token::False };

        assert_eq!(expr_stmt.token, expected_token);
        let boolean_expr = if let Expr::Boolean(x) = &expr_stmt.expr {
            x
        } else {
            panic!("Expect type is Expr::Boolean");
        };
        assert_eq!(boolean_expr.token, expected_token);
        assert_eq!(
            *boolean_expr,
            ast::Boolean {
                token: expected_token,
                value: v
            }
        );
    }

    fn test_let_by_stmt(stmt: &ast::Stmt, id: &Id, v: &Val) {
        let let_stmt = if let Stmt::Let(x) = stmt {
            x
        } else {
            panic!("Expect type is Stmt::Let");
        };

        assert_eq!(let_stmt.token, Token::Let);
        test_identifier(&let_stmt.name, id.0);
        test_expr(&let_stmt.value, v);
    }

    fn test_return_by_stmt(stmt: &Stmt, v: &Val) {
        let return_stmt = if let Stmt::Return(x) = stmt {
            x
        } else {
            panic!("Expect type is Stmt::Return");
        };

        assert_eq!(return_stmt.token, Token::Return);
        test_expr(&return_stmt.return_value, v);
    }

    fn test_identifier_by_stmt(stmt: &Stmt, literal: &str) {
        let expr_stmt = if let Stmt::ExprStmt(x) = stmt {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt");
        };

        assert_eq!(expr_stmt.token, Token::Ident(literal.into()));

        let identifier = if let Expr::Identifier(x) = &expr_stmt.expr {
            x
        } else {
            panic!("Expect type is Expr::Identifier");
        };
        test_identifier(&identifier, literal);
    }

    fn test_interger_by_stmt(stmt: &Stmt, v: i64) {
        let expr_stmt = if let Stmt::ExprStmt(x) = stmt {
            x
        } else {
            panic!("Expect type is Stmt::ExprStmt");
        };

        assert_eq!(expr_stmt.token, Token::Int(v.to_string()));

        let integer = if let Expr::Integer(x) = &expr_stmt.expr {
            x
        } else {
            panic!("Expect type is Expr::Integer");
        };
        test_integer(&integer, v);
    }

    fn test_integer(integer: &ast::Integer, v: i64) {
        assert_eq!(
            *integer,
            ast::Integer {
                token: Token::Int(v.to_string()),
                value: v.into()
            }
        );
    }

    fn test_identifier(identifier: &ast::Identifier, literal: &str) {
        assert_eq!(
            *identifier,
            ast::Identifier {
                token: Token::Ident(literal.into()),
                value: literal.into(),
            }
        );
    }

    fn test_parse(input: &str) -> ast::Program {
        let lexer = Lexer::new(input.to_string());
        let mut parser = Parser::new(lexer);
        parser.parse_program().unwrap()
    }

    fn test_expr(expr: &Expr, v: &Val) {
        match v {
            Val::S(v) => assert_eq!(
                *expr,
                Expr::StringLit(ast::StringLit {
                    token: Token::StringLiteral(v.to_string()),
                    value: v.to_string()
                })
            ),
            Val::B(v) => assert_eq!(
                *expr,
                Expr::Boolean(ast::Boolean {
                    token: match v {
                        true => Token::True,
                        false => Token::False,
                    },
                    value: *v
                })
            ),
            Val::Id(v) => assert_eq!(
                *expr,
                Expr::Identifier(ast::Identifier {
                    token: Token::Ident(v.0.to_string()),
                    value: v.0.to_string()
                })
            ),
            Val::I(v) => assert_eq!(
                *expr,
                Expr::Integer(ast::Integer {
                    token: Token::Int(v.to_string()),
                    value: *v
                })
            ),
            Val::Infix(l, o, r) => test_infix_by_expr(expr, l, o, r),
        }
    }
}
