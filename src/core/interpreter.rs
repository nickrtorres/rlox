use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

use super::{
    Expr, LoxCallable, LoxClass, LoxInstance, Object, Result, RloxError, Stmt, Token, TokenType,
    INIT_METHOD,
};

const THIS: &'static str = "this";

/// Checks if an Rc is unique
///
/// Returns RloxError::NonUniqueRc is the strong count or weak_count is greater
/// than 1
fn fail_if_not_unique<T>(ptr: &Rc<T>) -> Result<()> {
    if Rc::strong_count(ptr) > 1 || Rc::weak_count(ptr) > 1 {
        return Err(RloxError::NonUniqueRc);
    }

    Ok(())
}

#[derive(Debug, Clone)]
pub struct Environment {
    values: HashMap<String, Object>,
    enclosing: Option<Rc<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            values: HashMap::new(),
            enclosing: None,
        }
    }

    pub fn from(enclosing: &Rc<Environment>) -> Self {
        Environment {
            values: HashMap::new(),
            enclosing: Some(Rc::clone(enclosing)),
        }
    }

    pub fn define(&mut self, name: String, value: Object) {
        self.values.insert(name, value);
        assert!(!self.values.is_empty());
    }

    fn get(&self, name: &str) -> Result<Object> {
        match self.values.get(name) {
            Some(s) => Ok(s.clone()),
            None => {
                if let Some(e) = &self.enclosing {
                    return e.get(name);
                }

                Err(RloxError::UndefinedVariable)
            }
        }
    }

    fn assign(&mut self, name: &str, value: Object) -> Result<Object> {
        match self.values.entry(name.to_owned()) {
            Entry::Vacant(_) => {
                if let Some(e) = &mut self.enclosing {
                    fail_if_not_unique(&e)?;
                    return Rc::get_mut(e)
                        .ok_or_else(|| unreachable!())
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
        let enclosing = self.enclosing.take().ok_or_else(|| unreachable!())?;

        // we're about to consume enclosing! make sure there aren't any other users
        fail_if_not_unique(&enclosing)?;
        *self = Rc::try_unwrap(enclosing).map_err(|_| unreachable!())?;

        Ok(())
    }

    fn get_at(&self, distance: usize, name: &str) -> Result<Object> {
        self.ancestor(distance, |values| {
            values
                .ok_or(RloxError::UndefinedVariable)
                .and_then(|e| e.get(name))
        })
    }

    fn ancestor<F: FnOnce(Option<Rc<Environment>>) -> Result<Object>>(
        &self,
        distance: usize,
        f: F,
    ) -> Result<Object> {
        let mut environment: Option<Rc<Environment>> = Some(Rc::new(self.clone()));
        for _ in 0..(distance) {
            assert!(environment
                .as_ref()
                .map_or(false, |e| e.enclosing.is_some()));

            // TODO: yikes!
            environment = environment.map(|e| Rc::clone(&e.enclosing.as_ref().unwrap()))
        }

        f(environment)
    }
}

#[derive(Debug)]
pub struct Interpreter {
    pub environment: Rc<Environment>,
    pub locals: HashMap<Expr, usize>,
}

impl Interpreter {
    // TODO: Not using global environment like jlox. Maybe this is bad.
    pub fn new() -> Self {
        let clock_fn = LoxCallable::Clock;
        let mut environment = Environment::new();
        environment.define("clock".to_owned(), Object::Callable(clock_fn));
        Interpreter {
            environment: Rc::new(environment),
            locals: HashMap::new(),
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
                fail_if_not_unique(&self.environment)?;
                self.execute_block(statements, Environment::from(&self.environment))?;
            }
            Stmt::If(expr, then_branch, else_branch) => {
                if let Object::Bool(true) = self.evaluate(&expr)? {
                    self.execute(then_branch)?;
                } else if let Some(e) = else_branch {
                    self.execute(e)?;
                }
            }
            Stmt::Class(name, superclass, methods) => {
                let superclass: Option<Box<LoxClass>> = if let Some(s) = superclass {
                    if let Object::Callable(LoxCallable::ClassDefinition(s)) = self.evaluate(s)? {
                        if s.name == name.lexeme {
                            // placeholder
                            return Err(RloxError::InheritNonClass);
                        }
                        Some(Box::new(s))
                    } else {
                        // TODO valid state?
                        None
                    }
                } else {
                    None
                };

                let mut klass = LoxClass::new(name.lexeme.clone(), superclass);

                // Methods are of type Stmt
                //   The underlying variant *should* be Stmt::Function
                //     - TODO can this be an invariant?
                for method in methods {
                    if let Stmt::Function(LoxCallable::UserDefined(f)) = method {
                        let mut f = f.clone();
                        f.initializer = f.name.lexeme == INIT_METHOD.to_owned();
                        klass.add_method(f);
                    } else {
                        unreachable!();
                    }
                }

                let klass = Object::Callable(LoxCallable::ClassDefinition(klass));
                fail_if_not_unique(&self.environment)?;
                Rc::get_mut(&mut self.environment)
                    .map(|e| e.define(name.lexeme.clone(), klass))
                    .ok_or_else(|| unreachable!())?;
            }
            Stmt::Expression(expr) => {
                self.evaluate(&expr)?;
            }
            Stmt::Print(expr) => {
                let value = self.evaluate(&expr)?;
                println!("{}", value);
            }
            Stmt::Var(token, Some(expr)) => {
                let value = match self.evaluate(&expr)? {
                    Object::Callable(LoxCallable::ClassInstance(c)) => {
                        // If we just initialized a class instance then we need to
                        // replace the 'this' variable in our environment with ourselves
                        //
                        // If this variable does not exist, then we didn't run a user defined
                        // constructor. This is not an error. We'll just propogate the original
                        // instance.
                        match self.environment.get(THIS) {
                            Ok(t) => t,
                            Err(RloxError::UndefinedVariable) => {
                                Object::Callable(LoxCallable::ClassInstance(c))
                            }
                            _ => unreachable!(),
                        }
                    }
                    v => v,
                };

                Rc::get_mut(&mut self.environment)
                    .map(|e| e.define(token.lexeme.clone(), value))
                    .ok_or_else(|| unreachable!())?;
            }
            Stmt::While(condition, stmt) => {
                while let Object::Bool(true) = self.evaluate(&condition)? {
                    self.execute(&stmt)?;
                }
            }
            Stmt::Function(f) => {
                let name = match f {
                    LoxCallable::UserDefined(s) => &s.name.lexeme,
                    _ => unreachable!(),
                };

                fail_if_not_unique(&self.environment)?;
                Rc::get_mut(&mut self.environment)
                    .map(|e| e.define(name.to_owned(), Object::Callable(f.clone())))
                    .ok_or_else(|| unreachable!())?;
            }
            Stmt::Return(_, value) => {
                let mut v = Object::Nil;
                if let Some(c) = value {
                    v = self.evaluate(c)?;
                }

                return Err(RloxError::Return(v));
            }
            _ => {}
        }

        Ok(())
    }

    pub fn execute_block(&mut self, statements: &[Stmt], environment: Environment) -> Result<()> {
        self.environment = Rc::new(environment);
        for statement in statements {
            if let Err(e) = self.execute(statement) {
                match e {
                    // Make sure to flatten our environment before returning a
                    // value to the caller
                    RloxError::Return(v) => {
                        fail_if_not_unique(&self.environment)?;
                        Rc::get_mut(&mut self.environment)
                            .ok_or_else(|| unreachable!())
                            .and_then(Environment::flatten)?;
                        return Err(RloxError::Return(v));
                    }
                    _ => return Err(e),
                }
            }
        }

        fail_if_not_unique(&self.environment)?;
        Rc::get_mut(&mut self.environment)
            .ok_or_else(|| unreachable!())
            .and_then(Environment::flatten)?;
        Ok(())
    }

    fn evaluate(&mut self, expr: &Expr) -> Result<Object> {
        match expr {
            Expr::Assign(token, expr) => {
                let value = self.evaluate(expr)?;
                Rc::get_mut(&mut self.environment)
                    .ok_or_else(|| unreachable!())
                    .and_then(|e| e.assign(&token.lexeme, value))
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
                    _ => unreachable!(),
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

                unreachable!();
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
            Expr::Get(object, name) => {
                if let Object::Callable(LoxCallable::ClassInstance(c)) = self.evaluate(object)? {
                    c.get(&name.lexeme)
                } else {
                    Err(RloxError::PropertyAccessOnNonInstance)
                }
            }
            Expr::Grouping(group) => self.evaluate(group),
            Expr::Variable(token) => Ok(self.look_up_variable(&token.lexeme, expr)?),
            Expr::Call(callee, _, args) => {
                let function = self.evaluate(callee).and_then(|fun| match fun {
                    Object::Callable(c) => Ok(c),
                    _ => unreachable!(),
                })?;

                let mut arguments = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    arguments.push(self.evaluate(arg)?);
                }

                if arguments.len() != function.arity() {
                    return Err(RloxError::ArgumentMismatch(
                        function.arity(),
                        arguments.len(),
                    ));
                }

                match function {
                    // TODO: handle SystemTime::now failing
                    LoxCallable::Clock => SystemTime::now()
                        .duration_since(UNIX_EPOCH)
                        .map_err(|_| unimplemented!())
                        .map(|t| Object::Time(t.as_millis())),
                    LoxCallable::UserDefined(f) => {
                        assert_eq!(f.parameters.len(), arguments.len());

                        // The 'this' pointer needs to be defined in our parent environment.
                        if let Some(instance) = f.this {
                            Rc::get_mut(&mut self.environment)
                                .and_then(|e| {
                                    e.define(
                                        THIS.to_owned(),
                                        Object::Callable(LoxCallable::ClassInstance(instance)),
                                    );

                                    Some(())
                                })
                                .ok_or_else(|| unreachable!())?;
                        }

                        if let Some(superclass) = f.super_class {
                            Rc::get_mut(&mut self.environment)
                                .map(|e| {
                                    e.define(
                                        "super".to_owned(),
                                        Object::Callable(LoxCallable::ClassDefinition(superclass)),
                                    )
                                })
                                .ok_or_else(|| unreachable!())?;
                        }

                        let mut environment = Environment::from(&self.environment);

                        // TODO: don't clone
                        for (param, arg) in f.parameters.iter().zip(arguments.iter()) {
                            environment.define(param.lexeme.clone(), arg.clone())
                        }

                        if let Err(e) = self.execute_block(&f.body, environment) {
                            match e {
                                RloxError::Return(v) => {
                                    if f.initializer {
                                        return self.environment.get(THIS);
                                    } else {
                                        return Ok(v);
                                    }
                                }
                                _ => return Err(e),
                            }
                        } else {
                            if f.initializer {
                                return self.environment.get(THIS);
                            } else {
                                return Ok(Object::Nil);
                            }
                        }
                    }
                    LoxCallable::ClassDefinition(class) => {
                        let superclass = class.superclass.clone();
                        let instance = LoxInstance::new(class, superclass);
                        if let Ok(Object::Callable(LoxCallable::UserDefined(f))) =
                            instance.get("init")
                        {
                            let init_expr = Box::new(Expr::Call(
                                Box::new(Expr::Literal(Object::Callable(
                                    LoxCallable::UserDefined(f),
                                ))),
                                Token::default(),
                                args.clone(),
                            ));

                            self.evaluate(&init_expr)?;
                        }

                        Ok(Object::Callable(LoxCallable::ClassInstance(instance)))
                    }
                    _ => unimplemented!(),
                }
            }
            Expr::Set(object, name, value) => {
                // TODO Yikes. Maybe it's a good idea to store the instance name within the
                // instance?
                let instance_name = match &**object {
                    Expr::Variable(t) | Expr::This(t) => &t.lexeme,
                    _ => unreachable!(),
                };

                if let Object::Callable(LoxCallable::ClassInstance(mut instance)) =
                    self.evaluate(object)?
                {
                    let value = self.evaluate(value)?;
                    instance.set(&name.lexeme, value);

                    // Note: jlox relies on implicit mutation of the environment.  rlox's
                    // environment hands out copies of objects rather than references.  We need to
                    // manually update the environment after setting a field on a variable.
                    Rc::get_mut(&mut self.environment)
                        .and_then(|e| {
                            e.assign(
                                &instance_name,
                                Object::Callable(LoxCallable::ClassInstance(instance.clone())),
                            )
                            .ok()
                        })
                        .ok_or_else(|| unreachable!())?;

                    // We just added this value. It must be `Ok`
                    match instance.get(&name.lexeme) {
                        Ok(v) => Ok(v),
                        Err(e) => unreachable!("{:?}", e),
                    }
                } else {
                    Err(RloxError::PropertyAccessOnNonInstance)
                }
            }
            Expr::This(keyword) => Ok(self.look_up_variable(&keyword.lexeme, expr)?),
            Expr::Super(_, method) => {
                let superclass = self.look_up_variable("super", expr)?;
                if let Object::Callable(LoxCallable::ClassDefinition(c)) = superclass {
                    if c.methods.iter().any(|m| m.name.lexeme == method.lexeme) {
                        if let Object::Callable(LoxCallable::ClassInstance(c)) =
                            self.environment.get("this")?
                        {
                            return c.get_super(&method.lexeme);
                        } else {
                            unreachable!(); // ?
                        }
                    } else {
                        return Err(RloxError::UndefinedProperty);
                    }
                } else {
                    unreachable!();
                }
            }
        }
    }

    fn look_up_variable(&mut self, name: &str, expr: &Expr) -> Result<Object> {
        self.locals.get(expr).map_or_else(
            || self.environment.get(name),
            |distance| self.environment.get_at(*distance, name),
        )
    }

    pub fn resolve(&mut self, map: HashMap<Expr, usize>) {
        self.locals.extend(map.into_iter());
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

    #[test]
    fn it_supports_empty_fun() {
        let scanner = Scanner::new("fun f() {}".to_owned());
        let parser = Parser::new(scanner.scan_tokens());
        let mut vec_stmts = parser.parse_stmts().unwrap();
        let mut stmts = vec_stmts.drain(..);
        let mut interpreter = Interpreter::new();
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
    }
}
