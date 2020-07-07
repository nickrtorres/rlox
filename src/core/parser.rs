use std::cell::Cell;
use std::mem::discriminant;

use super::{Expr, FunctionStmt, LoxCallable, Object, Result, RloxError, Stmt, Token, TokenType};

/// Parses a series of Tokens into an abstract syntax tree
///
/// Parser implements Lox's grammer show below:
/// ```notrust
///   expression     → equality ;
///   equality       → comparison ( ( "!=" | "==" ) comparison )* ;
///   comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
///   addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
///   multiplication → unary ( ( "/" | "*" ) unary )* ;
///   unary          → ( "!" | "-" ) unary
///                  | primary ;
///   primary        → NUMBER | STRING | "false" | "true" | "nil"
///                  | "(" expression ")" ;
///   program        → statement* EOF ;
///   statement      → exprStmt
///                  | printStmt ;
///   exprStmt       → expression ";" ;
///   printStmt      → "print" expression ";" ;
/// ```
///
/// `Parser` is **not** thread safe. Internally, `Parser` uses interior
/// mutability to manage it's internal cursor for the current, next, and
/// previous tokens. This is an implementation detail most end users don't need
/// to worry about.
pub struct Parser {
    tokens: Vec<Token>,
    /// cursor is an implementation detail end users shouldn't worry about. Use
    /// interior mutability here to avoid forcing the user to hold a mutable Parser.
    cursor: Cell<usize>,
}

impl Parser {
    #[must_use]
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            cursor: Cell::new(0),
        }
    }

    pub fn parse_stmts(self) -> Result<Vec<Stmt>> {
        let mut statements: Vec<Stmt> = Vec::new();

        while !self.is_at_end() {
            statements.push(self.declaration()?);
        }

        Ok(statements)
    }

    fn declaration(&self) -> Result<Stmt> {
        if self.match_tokens(vec![TokenType::Class]) {
            return self.class_declaration();
        }

        if self.match_tokens(vec![TokenType::Fun]) {
            return self.function();
        }

        if self.match_tokens(vec![TokenType::Var]) {
            return self.var_declaration().map_err(|e| {
                self.synchronize();
                e
            });
        }

        self.statement().map_err(|e| {
            self.synchronize();
            e
        })
    }

    fn class_declaration(&self) -> Result<Stmt> {
        let name = self.consume(TokenType::Identifier)?;
        self.consume(TokenType::LeftBrace)?;

        let mut methods = Vec::new();
        while !self.check(&TokenType::RightBrace) && !self.is_at_end() {
            methods.push(self.function()?);
        }

        self.consume(TokenType::RightBrace)?;

        Ok(Stmt::Class(name, methods))
    }

    fn function(&self) -> Result<Stmt> {
        let name = self.consume(TokenType::Identifier)?;
        self.consume(TokenType::LeftParen)?;
        let mut parameters = Vec::new();

        // TODO why does `check` take a ref?
        if !self.check(&TokenType::RightParen) {
            loop {
                if parameters.len() >= 255 {
                    // TODO define actual TooManyArgs err
                    unimplemented!();
                }

                parameters.push(self.consume(TokenType::Identifier)?);

                if !self.match_tokens(vec![TokenType::Comma]) {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen)?;
        self.consume(TokenType::LeftBrace)?;
        let body = self.block()?;

        Ok(Stmt::Function(LoxCallable::UserDefined(FunctionStmt {
            name,
            parameters,
            body,
            this: None,
            initializer: false,
        })))
    }

    fn var_declaration(&self) -> Result<Stmt> {
        let name = self.consume(TokenType::Identifier)?;

        let initializer = if self.match_tokens(vec![TokenType::Equal]) {
            Some(*(self.expression()?))
        } else {
            None
        };

        let _ = self.consume(TokenType::Semicolon);
        Ok(Stmt::Var(name, initializer))
    }

    fn statement(&self) -> Result<Stmt> {
        if self.match_tokens(vec![TokenType::For]) {
            return self.for_statement();
        } else if self.match_tokens(vec![TokenType::If]) {
            return self.if_statement();
        } else if self.match_tokens(vec![TokenType::Print]) {
            self.print_statement()
        } else if self.match_tokens(vec![TokenType::Return]) {
            self.return_statement()
        } else if self.match_tokens(vec![TokenType::While]) {
            self.while_statement()
        } else if self.match_tokens(vec![TokenType::LeftBrace]) {
            Ok(Stmt::Block(self.block()?))
        } else {
            self.expression_statement()
        }
    }

    fn return_statement(&self) -> Result<Stmt> {
        let keyword = self.previous()?;

        let value = if !self.check(&TokenType::Semicolon) {
            Some(*self.expression()?)
        } else {
            None
        };

        self.consume(TokenType::Semicolon)?;
        Ok(Stmt::Return(keyword, value))
    }

    fn for_statement(&self) -> Result<Stmt> {
        self.consume(TokenType::LeftParen)?;

        let initializer = if self.match_tokens(vec![TokenType::Semicolon]) {
            None
        } else if self.match_tokens(vec![TokenType::Var]) {
            Some(self.var_declaration()?)
        } else {
            Some(self.expression_statement()?)
        };

        let condition = if !self.check(&TokenType::Semicolon) {
            *self.expression()?
        } else {
            Expr::Literal(Object::Bool(true))
        };

        self.consume(TokenType::Semicolon)?;

        let increment = if !self.check(&TokenType::RightParen) {
            Some(*self.expression()?)
        } else {
            None
        };

        self.consume(TokenType::RightParen)?;

        let mut body = self.statement()?;
        if let Some(increment) = increment {
            body = Stmt::Block(vec![body, Stmt::Expression(increment)]);
        }

        body = Stmt::While(condition, Box::new(body));

        if let Some(initializer) = initializer {
            body = Stmt::Block(vec![initializer, body]);
        }

        Ok(body)
    }

    fn while_statement(&self) -> Result<Stmt> {
        self.consume(TokenType::LeftParen)?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen)?;
        let body = self.statement()?;

        Ok(Stmt::While(*condition, Box::new(body)))
    }

    fn if_statement(&self) -> Result<Stmt> {
        self.consume(TokenType::LeftParen)?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen)?;

        let then_branch = self.statement()?;
        let else_branch = if self.match_tokens(vec![TokenType::Else]) {
            Some(Box::new(self.statement()?))
        } else {
            None
        };

        Ok(Stmt::If(*condition, Box::new(then_branch), else_branch))
    }

    fn block(&self) -> Result<Vec<Stmt>> {
        let mut statements = Vec::new();

        while !self.check(&TokenType::RightBrace) && !self.is_at_end() {
            statements.push(self.declaration()?);
        }

        self.consume(TokenType::RightBrace)?;
        Ok(statements)
    }

    fn synchronize(&self) {
        self.advance();

        while !self.is_at_end() {
            if let Ok(token) = self.previous() {
                if token.token_type == TokenType::Semicolon {
                    return;
                }
            }

            if let Some(token) = self.peek() {
                match token.token_type {
                    TokenType::Class
                    | TokenType::Fun
                    | TokenType::Var
                    | TokenType::If
                    | TokenType::While
                    | TokenType::Print
                    | TokenType::Return => return,
                    _ => {}
                }
            }

            self.advance();
        }
    }

    fn print_statement(&self) -> Result<Stmt> {
        let value = self.expression()?;
        self.consume(TokenType::Semicolon)?;
        Ok(Stmt::Print(*value))
    }

    fn expression_statement(&self) -> Result<Stmt> {
        let value = self.expression()?;
        self.consume(TokenType::Semicolon)?;
        Ok(Stmt::Expression(*value))
    }

    /// Parse Lox's grammer into an AST
    pub fn parse(&self) -> Result<Box<Expr>> {
        self.expression()
    }

    fn expression(&self) -> Result<Box<Expr>> {
        self.assignment()
    }

    fn assignment(&self) -> Result<Box<Expr>> {
        let expr = self.or()?;

        if self.match_tokens(vec![TokenType::Equal]) {
            let value = self.assignment()?;

            match *expr {
                Expr::Variable(token) => return Ok(Box::new(Expr::Assign(token, value))),
                Expr::Get(object, name) => return Ok(Box::new(Expr::Set(object, name, value))),
                _ => return Err(RloxError::InvalidAssignment),
            };
        }

        Ok(expr)
    }

    fn or(&self) -> Result<Box<Expr>> {
        let mut expr = self.and()?;

        while self.match_tokens(vec![TokenType::Or]) {
            let operator = self.previous()?;
            let right = self.and()?;
            expr = Box::new(Expr::Logical(expr, operator, right));
        }

        Ok(expr)
    }

    fn and(&self) -> Result<Box<Expr>> {
        let mut expr = self.equality()?;

        while self.match_tokens(vec![TokenType::And]) {
            let operator = self.previous()?;
            let right = self.and()?;
            expr = Box::new(Expr::Logical(expr, operator, right));
        }

        Ok(expr)
    }

    fn equality(&self) -> Result<Box<Expr>> {
        let mut expr = self.comparison()?;

        while self.match_tokens(vec![TokenType::BangEqual, TokenType::EqualEqual]) {
            let operator = self.previous()?;
            let right = self.comparison()?;

            expr = Box::new(Expr::Binary(expr, operator, right));
        }

        Ok(expr)
    }

    fn comparison(&self) -> Result<Box<Expr>> {
        let mut expr = self.addition()?;

        while self.match_tokens(vec![
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let operator = self.previous()?;
            let right = self.addition()?;
            expr = Box::new(Expr::Binary(expr, operator, right));
        }

        Ok(expr)
    }

    fn addition(&self) -> Result<Box<Expr>> {
        let mut expr = self.multiplication()?;

        while self.match_tokens(vec![TokenType::Minus, TokenType::Plus]) {
            let operator = self.previous()?;
            let right = self.multiplication()?;

            expr = Box::new(Expr::Binary(expr, operator, right));
        }

        Ok(expr)
    }

    fn multiplication(&self) -> Result<Box<Expr>> {
        let mut expr = self.unary()?;

        while self.match_tokens(vec![TokenType::Slash, TokenType::Star]) {
            let operator = self.previous()?;
            let right = self.unary()?;

            expr = Box::new(Expr::Binary(expr, operator, right));
        }

        Ok(expr)
    }

    fn unary(&self) -> Result<Box<Expr>> {
        if self.match_tokens(vec![TokenType::Bang, TokenType::Minus]) {
            let operator = self.previous()?;
            let right = self.unary()?;

            return Ok(Box::new(Expr::Unary(operator, right)));
        }

        self.call()
    }

    fn call(&self) -> Result<Box<Expr>> {
        let mut expr = self.primary()?;

        loop {
            if self.match_tokens(vec![TokenType::LeftParen]) {
                expr = self.finish_call(expr)?;
            } else if self.match_tokens(vec![TokenType::Dot]) {
                let name = self.consume(TokenType::Identifier)?;
                expr = Box::new(Expr::Get(expr, name));
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn finish_call(&self, callee: Box<Expr>) -> Result<Box<Expr>> {
        let mut arguments = Vec::new();

        if !self.check(&TokenType::RightParen) {
            loop {
                if arguments.len() >= 255 {
                    // TODO: handle this case
                    unimplemented!();
                }

                arguments.push(*self.expression()?);

                if !self.match_tokens(vec![TokenType::Comma]) {
                    break;
                }
            }
        }

        let paren = self.consume(TokenType::RightParen)?;
        Ok(Box::new(Expr::Call(callee, paren, arguments)))
    }

    fn primary(&self) -> Result<Box<Expr>> {
        if self.match_tokens(vec![TokenType::False]) {
            return Ok(Box::new(Expr::Literal(Object::Bool(false))));
        }
        if self.match_tokens(vec![TokenType::True]) {
            return Ok(Box::new(Expr::Literal(Object::Bool(true))));
        }
        if self.match_tokens(vec![TokenType::Nil]) {
            return Ok(Box::new(Expr::Literal(Object::Nil)));
        }

        // TODO: constructing variants for Number and String isn't ideal
        if self.match_tokens(vec![
            TokenType::Number(f64::from(0)),
            TokenType::String(String::new()),
        ]) {
            let previous = self.previous()?;
            let rv = match &previous.token_type {
                TokenType::Number(n) => Ok(Box::new(Expr::Literal(Object::Number(*n)))),
                TokenType::String(s) => Ok(Box::new(Expr::Literal(Object::String(s.to_owned())))),
                _ => unreachable!(),
            };

            return rv;
        }

        if self.match_tokens(vec![TokenType::This]) {
            return Ok(Box::new(Expr::This(self.previous()?)));
        }

        if self.match_tokens(vec![TokenType::Identifier]) {
            return Ok(Box::new(Expr::Variable(self.previous()?)));
        }

        if self.match_tokens(vec![TokenType::LeftParen]) {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen)?;
            return Ok(Box::new(Expr::Grouping(expr)));
        }

        // TODO is this reachable?
        unimplemented!();
    }

    fn consume(&self, token_type: TokenType) -> Result<Token> {
        if !self.check(&token_type) {
            // We already consumed the problematic token.  We need to step back
            // for a second to grab the bad line number. It should be *impossible*
            // for the token we just consumed to not be there.
            let line = self.previous().map_err(|_| unreachable!())?.line;

            match token_type {
                TokenType::RightParen => return Err(RloxError::UnclosedParenthesis(line)),
                TokenType::Semicolon => return Err(RloxError::MissingSemicolon(line)),
                _ => unreachable!(),
            }
        }

        // We just validated the next token. It must exist.
        self.advance().ok_or_else(|| unreachable!())
    }

    // TODO: this should not be a vec. it should be a slice or an iterator
    //
    // maybe this should just be an if statement
    fn match_tokens(&self, token_types: Vec<TokenType>) -> bool {
        token_types
            .into_iter()
            .any(|token_type| self.check(&token_type))
            .then_some(())
            .and_then(|_| self.advance())
            .is_some()
    }

    fn check(&self, token_type: &TokenType) -> bool {
        if self.is_at_end() {
            return false;
        }

        self.peek().map_or(false, move |t| {
            discriminant(&t.token_type) == discriminant(&token_type)
        })
    }

    fn is_at_end(&self) -> bool {
        self.peek()
            .map_or(false, |t| t.token_type == TokenType::Eof)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.cursor.get())
    }

    fn previous(&self) -> Result<Token> {
        debug_assert!(self.cursor.get() > 0);
        self.tokens
            .get(self.cursor.get() - 1)
            .ok_or(RloxError::NoPrevious)
            .map(|t| t.clone())
    }

    fn advance(&self) -> Option<Token> {
        if !self.is_at_end() {
            let old = self.cursor.get();
            self.cursor.replace(old + 1);
        }

        self.previous().ok()
    }
}

// TODO try to figure out a way not to do this
#[cfg(test)]
use super::Scanner;
mod tests {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn it_can_advance_over_token_iterator() {
        let scanner = Scanner::new("var breakfast;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());

        assert_eq!(
            Some(Token::new(TokenType::Var, String::from("var"), 1)),
            parser.advance()
        );
        assert_eq!(
            Some(Token::new(
                TokenType::Identifier,
                String::from("breakfast"),
                1
            )),
            parser.advance()
        );
        assert_eq!(
            Some(Token::new(TokenType::Semicolon, String::from(";"), 1)),
            parser.advance()
        );

        assert_eq!(
            Some(Token::new(TokenType::Semicolon, String::from(";"), 1)),
            parser.advance()
        );
    }

    #[test]
    fn it_can_parse_a_float() {
        let scanner = Scanner::new("1".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Literal(Object::Number(1 as f64)),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_bool() {
        let scanner = Scanner::new("true".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Expr::Literal(Object::Bool(true)), *parser.parse().unwrap());
    }

    #[test]
    fn it_can_parse_nil() {
        let scanner = Scanner::new("nil".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Expr::Literal(Object::Nil), *parser.parse().unwrap());
    }

    #[test]
    fn it_can_parse_a_unary_expression() {
        let scanner = Scanner::new("-1".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Unary(
                Token::new(TokenType::Minus, "-".to_owned(), 1),
                Box::new(Expr::Literal(Object::Number(1 as f64)))
            ),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_binary_expression() {
        let scanner = Scanner::new("1 + 2".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Binary(
                Box::new(Expr::Literal(Object::Number(1 as f64))),
                Token::new(TokenType::Plus, "+".to_owned(), 1),
                Box::new(Expr::Literal(Object::Number(2 as f64)))
            ),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_grouping_expression() {
        let scanner = Scanner::new("(1)".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Grouping(Box::new(Expr::Literal(Object::Number(1 as f64)))),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_compound_expression() {
        let scanner = Scanner::new("(1 + 2) * 3".to_owned());
        let parser = Parser::new(scanner.scan_tokens());

        let plus = Token::new(TokenType::Plus, "+".to_owned(), 1);
        let add_expr = Expr::Grouping(Box::new(Expr::Binary(
            Box::new(Expr::Literal(Object::Number(1 as f64))),
            plus,
            Box::new(Expr::Literal(Object::Number(2 as f64))),
        )));

        let star = Token::new(TokenType::Star, "*".to_owned(), 1);
        let expected = Expr::Binary(
            Box::new(add_expr),
            star,
            Box::new(Expr::Literal(Object::Number(3 as f64))),
        );

        assert_eq!(expected, *parser.parse().unwrap());
    }

    #[test]
    fn it_can_parse_an_arbitrarily_complex_expression() {
        let scanner = Scanner::new("(1 + 2) * 3 > (4 - 5) / 6".to_owned());
        let parser = Parser::new(scanner.scan_tokens());

        let plus = Token::new(TokenType::Plus, "+".to_owned(), 1);
        let add_expr = Expr::Grouping(Box::new(Expr::Binary(
            Box::new(Expr::Literal(Object::Number(1 as f64))),
            plus,
            Box::new(Expr::Literal(Object::Number(2 as f64))),
        )));

        let star = Token::new(TokenType::Star, "*".to_owned(), 1);
        let star_expr = Expr::Binary(
            Box::new(add_expr),
            star,
            Box::new(Expr::Literal(Object::Number(3 as f64))),
        );

        let minus = Token::new(TokenType::Minus, "-".to_owned(), 1);
        let sub_expr = Expr::Grouping(Box::new(Expr::Binary(
            Box::new(Expr::Literal(Object::Number(4 as f64))),
            minus,
            Box::new(Expr::Literal(Object::Number(5 as f64))),
        )));

        let slash = Token::new(TokenType::Slash, "/".to_owned(), 1);
        let slash_expr = Expr::Binary(
            Box::new(sub_expr),
            slash,
            Box::new(Expr::Literal(Object::Number(6 as f64))),
        );

        let greater = Token::new(TokenType::Greater, ">".to_owned(), 1);
        let expected = Expr::Binary(Box::new(star_expr), greater, Box::new(slash_expr));

        assert_eq!(expected, *parser.parse().unwrap());
    }

    #[test]
    fn it_detects_unclosed_parenthesis() {
        let scanner = Scanner::new("(1".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Err(RloxError::UnclosedParenthesis(1)), parser.parse());
    }

    #[test]
    fn it_can_parse_a_stmt() {
        let scanner = Scanner::new("var a = true;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert!(parser.parse_stmts().is_ok());
    }

    #[test]
    fn it_can_parse_a_block() {
        let scanner = Scanner::new("{ print \"hello\"; }".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert!(parser.parse_stmts().is_ok())
    }

    #[test]
    fn it_can_parse_a_nested_block() {
        let scanner = Scanner::new("{ { print \"hello\"; } }".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert!(parser.parse_stmts().is_ok())
    }

    #[test]
    fn it_can_parse_a_function() {
        let scanner = Scanner::new("fun a () { print \"hello\"; }".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert!(parser.parse_stmts().is_ok())
    }
}
