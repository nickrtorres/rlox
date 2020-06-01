use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

use super::{Expr, LoxCallable, Object, Result, RloxError, Stmt, Token, TokenType};

#[derive(Debug)]
struct Environment {
    values: HashMap<Rc<str>, Object>,
    enclosing: Option<Rc<Environment>>,
}

impl Environment {
    fn with_global(g: (&str, Object)) -> Self {
        let mut env = Environment {
            values: HashMap::new(),
            enclosing: None,
        };

        env.define(&Rc::from(g.0.to_owned()), g.1);
        env
    }

    fn from(enclosing: &Rc<Environment>) -> Self {
        Environment {
            values: HashMap::new(),
            enclosing: Some(Rc::clone(enclosing)),
        }
    }

    fn define(&mut self, name: &Rc<str>, value: Object) {
        self.values.insert(Rc::clone(name), value);
        assert!(self.values.len() > 0);
    }

    fn get(&self, name: &Token) -> Result<Object> {
        match self.values.get(&name.lexeme) {
            Some(s) => Ok(s.clone()),
            None => {
                if let Some(e) = &self.enclosing {
                    return e.get(name);
                }

                Err(RloxError::UndefinedVariable)
            }
        }
    }

    fn assign(&mut self, name: &Token, value: Object) -> Result<Object> {
        match self.values.entry(Rc::clone(&name.lexeme)) {
            Entry::Vacant(_) => {
                if let Some(e) = &mut self.enclosing {
                    assert_eq!(1, Rc::strong_count(&e));
                    return Rc::get_mut(e)
                        .ok_or(RloxError::Unreachable)
                        .and_then(|nested| nested.assign(name, value));
                }

                Err(RloxError::UndefinedVariable)
            }
            Entry::Occupied(mut e) => {
                e.insert(value);
                Ok(e.get().clone())
            }
        }
    }

    fn flatten(&mut self) -> Result<()> {
        let enclosing = self.enclosing.take().ok_or(RloxError::Unreachable)?;

        // we're about to consume enclosing! make sure there aren't any other users
        if Rc::strong_count(&enclosing) != 1 {
            return Err(RloxError::Unreachable);
        }

        *self = Rc::try_unwrap(enclosing).map_err(|_| RloxError::Unreachable)?;

        Ok(())
    }
}

pub struct Interpreter {
    environment: Rc<Environment>,
}

impl Interpreter {
    pub fn new() -> Self {
        let clock_fn = LoxCallable {
            arity: 0,
            call: |_, _| {
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map_err(|_| RloxError::Unreachable)
                    .map(|t| Object::Time(t.as_millis()))
            },
        };
        Interpreter {
            environment: Rc::new(Environment::with_global((
                "clock",
                Object::Callable(clock_fn),
            ))),
        }
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) -> Result<()> {
        for statement in statements {
            self.execute(&statement)?;
        }

        Ok(())
    }

    fn execute(&mut self, statement: &Stmt) -> Result<()> {
        match statement {
            Stmt::Block(statements) => {
                assert_eq!(1, Rc::strong_count(&self.environment));
                self.execute_block(statements, Environment::from(&self.environment))?;
            }
            Stmt::If(expr, then_branch, else_branch) => {
                if let Object::Bool(true) = self.evaluate(&expr)? {
                    self.execute(then_branch)?;
                } else if let Some(e) = else_branch {
                    self.execute(e)?;
                }
            }
            Stmt::Expression(expr) => {
                self.evaluate(&expr)?;
            }
            Stmt::Print(expr) => {
                let value = self.evaluate(&expr)?;
                println!("{}", value);
            }
            Stmt::Var(token, Some(expr)) => {
                let value = self.evaluate(&expr)?;
                Rc::get_mut(&mut self.environment)
                    .map(|e| e.define(&token.lexeme, value))
                    .ok_or(RloxError::Unreachable)?;
            }
            Stmt::While(condition, stmt) => {
                while let Object::Bool(true) = self.evaluate(&condition)? {
                    self.execute(&stmt)?;
                }
            }
            _ => {}
        }

        Ok(())
    }

    fn execute_block(&mut self, statements: &[Stmt], environment: Environment) -> Result<()> {
        self.environment = Rc::new(environment);
        for statement in statements {
            self.execute(statement)?;
        }

        assert_eq!(1, Rc::strong_count(&self.environment));
        Rc::get_mut(&mut self.environment)
            .ok_or(RloxError::Unreachable)
            .and_then(Environment::flatten)
    }

    fn evaluate(&mut self, expr: &Expr) -> Result<Object> {
        match expr {
            Expr::Assign(token, expr) => {
                let value = self.evaluate(expr)?;
                Rc::get_mut(&mut self.environment)
                    .ok_or(RloxError::Unreachable)
                    .and_then(|e| e.assign(&token, value))
            }
            Expr::Binary(left_expr, token, right_expr) => {
                let left = self.evaluate(left_expr)?;
                let right = self.evaluate(right_expr)?;

                match token.token_type {
                    TokenType::Minus => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Number(l - r)),
                        _ => Err(RloxError::MismatchedOperands(TokenType::Minus, left, right)),
                    },
                    TokenType::Slash => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Number(l / r)),
                        _ => Err(RloxError::MismatchedOperands(TokenType::Slash, left, right)),
                    },
                    TokenType::Star => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Number(l * r)),
                        _ => Err(RloxError::MismatchedOperands(TokenType::Star, left, right)),
                    },
                    TokenType::Plus => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Number(l + r)),
                        (Object::String(l), Object::String(r)) => {
                            let mut buffer = String::with_capacity(l.capacity() + r.capacity());
                            buffer.push_str(l);
                            buffer.push_str(r);
                            Ok(Object::String(buffer))
                        }
                        _ => Err(RloxError::MismatchedOperands(TokenType::Plus, left, right)),
                    },
                    TokenType::Greater => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Bool(l > r)),
                        _ => Err(RloxError::MismatchedOperands(TokenType::Plus, left, right)),
                    },
                    TokenType::GreaterEqual => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Bool(l >= r)),
                        _ => Err(RloxError::MismatchedOperands(TokenType::Plus, left, right)),
                    },
                    TokenType::Less => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Bool(l < r)),
                        _ => Err(RloxError::MismatchedOperands(TokenType::Plus, left, right)),
                    },
                    TokenType::LessEqual => match (&left, &right) {
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Bool(l <= r)),
                        _ => Err(RloxError::MismatchedOperands(TokenType::Plus, left, right)),
                    },
                    TokenType::BangEqual => Ok(Object::Bool(left != right)),
                    TokenType::EqualEqual => Ok(Object::Bool(left == right)),
                    _ => Err(RloxError::Unreachable),
                }
            }
            Expr::Unary(token, expr) => {
                let right = self.evaluate(expr)?;

                if let TokenType::Minus = token.token_type {
                    if let Object::Number(n) = right {
                        return Ok(Object::Number(f64::from(-1) * n));
                    }
                } else if let TokenType::Bang = token.token_type {
                    if let Object::Bool(b) = right {
                        return Ok(Object::Bool(!b));
                    } else {
                        return Ok(Object::Bool(!false));
                    }
                }

                Err(RloxError::Unreachable)
            }
            Expr::Literal(obj) => Ok(obj.clone()),
            Expr::Logical(left, token, right) => {
                let left = self.evaluate(left)?;

                if token.token_type == TokenType::Or {
                    if let Object::Bool(true) = left {
                        return Ok(left);
                    }
                } else {
                    if let Object::Bool(false) = left {
                        return Ok(left);
                    }
                }

                return self.evaluate(right);
            }
            Expr::Grouping(group) => self.evaluate(group),
            Expr::Variable(token) => Ok(self.environment.get(&token)?),
        }
    }
}

// TODO try to figure out a way not to do this
#[cfg(test)]
use super::{Parser, Scanner};
mod tests {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn it_can_evaluate_a_unary_expression() {
        let scanner = Scanner::new("-1".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(
            Ok(Object::Number(f64::from(-1))),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_can_evaluate_a_literal_expression() {
        let scanner = Scanner::new("true".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(Ok(Object::Bool(true)), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_a_literal_expression_nil() {
        let scanner = Scanner::new("nil".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Nil), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_mult() {
        let scanner = Scanner::new("6 * 7".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Ok(Object::Number(f64::from(42))),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_div() {
        let scanner = Scanner::new("8 / 4".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Ok(Object::Number(f64::from(8 / 4))),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_complex_notequal() {
        let scanner = Scanner::new("2 * 3 - 4 != 5 * 6 - 7".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Bool(true)), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_complex_equal() {
        let scanner = Scanner::new("(4 + 4) == (2 * 2 * 2)".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Bool(true)), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_string_concatenation() {
        let scanner = Scanner::new("\"foo\" + \"bar\"".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Ok(Object::String(String::from("foobar"))),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_identifies_mismatched_operands_plus() {
        let scanner = Scanner::new("1 + \"foo\"".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Plus,
                Object::Number(f64::from(1)),
                Object::String("foo".to_owned())
            )),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_identifies_mismatched_operands_minus() {
        let scanner = Scanner::new("1 - \"bar\"".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Minus,
                Object::Number(f64::from(1)),
                Object::String("bar".to_owned())
            )),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_identifies_mismatched_operands_star() {
        let scanner = Scanner::new("true * 1".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Star,
                Object::Bool(true),
                Object::Number(f64::from(1)),
            )),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_identifies_mismatched_operands_slash() {
        let scanner = Scanner::new("1 / nil".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Slash,
                Object::Number(f64::from(1)),
                Object::Nil
            )),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_recognizes_valid_statements_print_arithmetic() {
        let scanner = Scanner::new("print 1 + 1;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(statements.len(), 1);
        // todo yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_valid_statements_print_boolean() {
        let scanner = Scanner::new("print true;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(statements.len(), 1);
        // todo yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_valid_statements_print_string() {
        let scanner = Scanner::new("print \"foo\";".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(statements.len(), 1);
        // todo yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_valid_statements_print_nil() {
        let scanner = Scanner::new("print nil;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(statements.len(), 1);
        // todo yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_valid_statements_expression_arithmetic() {
        let scanner = Scanner::new("1 + 1;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(statements.len(), 1);
        // todo yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_valid_statements_expression_boolean() {
        let scanner = Scanner::new("true;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();

        assert_eq!(statements.len(), 1);
        // todo yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_valid_statements_expression_string() {
        let scanner = Scanner::new("\"foo\";".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_valid_statements_expression_nil() {
        let scanner = Scanner::new("nil;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();
        let mut interpreter = Interpreter::new();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(
            Ok(()),
            interpreter.execute(&statements.drain(..).next().unwrap())
        );
    }

    #[test]
    fn it_recognizes_invalid_statements_missing_semicolon() {
        let scanner = Scanner::new("print nil".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Err(RloxError::MissingSemicolon(1)), parser.parse_stmts());
    }

    #[test]
    fn it_supports_reassignment_block() {
        let scanner = Scanner::new("var a = 1; { a = 2; } print a;".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut vec_stmts = parser.parse_stmts().unwrap();
        let mut stmts = vec_stmts.drain(..);
        let mut interpreter = Interpreter::new();
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
    }

    #[test]
    fn it_supports_reassignment_nested_block() {
        let scanner = Scanner::new(
                        "var a = \"foo\"; { var b = \"bar\"; { var c = \"baz\"; print a + b + c; } print a + b; } print a;"
                            .to_owned(),
                    );
        let parser = Parser::new(scanner.scan_tokens());
        let mut vec_stmts = parser.parse_stmts().unwrap();
        let mut stmts = vec_stmts.drain(..);
        let mut interpreter = Interpreter::new();
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
    }
}
