use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use super::{
    find_method, ArithmeticOperation, Environment, Expr, Logical, LoxCallable, LoxClass,
    LoxInstance, Object, Result, RloxError, Stmt, Token, TokenType, INIT_METHOD,
};

const THIS: &str = "this";
const SUPER: &str = "super";

#[derive(Debug)]
pub struct Interpreter {
    pub environment: Environment,
    pub locals: HashMap<Expr, usize>,
}

impl Interpreter {
    // TODO: Not using global environment like jlox. Maybe this is bad.
    #[must_use]
    pub fn new() -> Self {
        Interpreter {
            environment: vec![("clock".to_owned(), Object::Callable(LoxCallable::Clock))]
                .into_iter()
                .collect::<Environment>(),
            locals: HashMap::new(),
        }
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) -> Result<()> {
        for statement in statements {
            self.execute(&statement)?;
        }

        Ok(())
    }

    fn validate_superclass(&mut self, superclass: &Option<Expr>) -> Result<Option<Box<LoxClass>>> {
        match superclass {
            Some(ref s) => {
                let klass = self.evaluate(s)?;
                if let Some(d) = klass.into_callable().and_then(LoxCallable::into_definition) {
                    return Ok(Some(Box::new(d)));
                } else {
                    return Err(RloxError::InheritNonClass);
                }
            }
            None => Ok(None),
        }
    }

    fn execute(&mut self, statement: &Stmt) -> Result<()> {
        match statement {
            Stmt::Block(statements) => {
                self.environment.raise();
                self.execute_block(statements, None)?;
            }
            Stmt::If(expr, then_branch, else_branch) => {
                if Interpreter::is_truthy(&self.evaluate(&expr)?) {
                    self.execute(then_branch)?;
                } else {
                    if let Some(e) = else_branch {
                        self.execute(e)?;
                    }
                }
            }
            Stmt::Class(name, superclass, methods) => {
                let superclass = self.validate_superclass(superclass)?;
                let mut klass = LoxClass::new(name.lexeme.clone(), superclass);

                for method in methods {
                    // The parser guarantees that a `method` is a Stmt::Function(...).
                    let mut f = method.clone().into_function_unchecked();
                    f.initializer = f.name.lexeme == INIT_METHOD;
                    klass.add_method(f);
                }

                let klass = Object::Callable(LoxCallable::ClassDefinition(klass));
                self.environment.define(name.lexeme.clone(), klass);
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
                            Err(RloxError::UndefinedVariable(_)) => {
                                Object::Callable(LoxCallable::ClassInstance(c))
                            }
                            _ => unreachable!(),
                        }
                    }
                    v => v,
                };

                self.environment.define(token.lexeme.clone(), value);
            }
            Stmt::Var(token, None) => {
                self.environment.define(token.lexeme.clone(), Object::Nil);
            }
            Stmt::While(condition, stmt) => {
                while let Object::Bool(true) = self.evaluate(&condition)? {
                    self.execute(&stmt)?;
                }
            }
            Stmt::Function(f) => {
                let mut f = f.clone();
                f.environment = self.environment.close_over();
                self.environment.define(
                    f.name.lexeme.to_owned(),
                    Object::Callable(LoxCallable::UserDefined(f.clone())),
                );
            }
            Stmt::Return(_, value) => {
                let mut v = Object::Nil;
                if let Some(c) = value {
                    v = self.evaluate(c)?;
                }

                return Err(RloxError::Return(v));
            }
        }

        Ok(())
    }

    pub fn execute_block(&mut self, statements: &[Stmt], callee: Option<&str>) -> Result<()> {
        for statement in statements {
            if let Err(e) = self.execute(statement) {
                match e {
                    // Make sure to lower our environment before returning a
                    // value to the caller
                    RloxError::Return(v) => {
                        self.environment.lower();
                        return Err(RloxError::Return(v));
                    }
                    _ => return Err(e),
                }
            }
        }

        if let Some(name) = callee {
            let this = self.environment.get(THIS)?;
            self.environment.assign(name, this)?;
        }
        self.environment.lower();
        Ok(())
    }

    fn evaluate(&mut self, expr: &Expr) -> Result<Object> {
        match expr {
            Expr::Assign(token, expr) => {
                let value = self.evaluate(expr)?;
                self.environment.assign(&token.lexeme, value)
            }
            Expr::Binary(left_expr, token, right_expr) => {
                let left = self.evaluate(left_expr)?;
                let right = self.evaluate(right_expr)?;

                match token.token_type {
                    TokenType::Minus => left - right,
                    TokenType::Slash => left / right,
                    TokenType::Star => left * right,
                    TokenType::Plus => left + right,
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
                match token.token_type {
                    TokenType::Minus => match right.into_number() {
                        Some(r) => Ok(Object::Number(-r)),
                        None => Err(RloxError::BadArithmeticOperation(
                            ArithmeticOperation::Negate,
                        )),
                    },
                    TokenType::Bang => match right {
                        Object::Bool(b) => Ok(Object::Bool(!b)),
                        // !false
                        _ => Ok(Object::Bool(true)),
                    },
                    _ => unreachable!(),
                }
            }
            Expr::Literal(obj) => Ok(obj.clone()),
            Expr::Logical(left, token, right) => {
                let left = self.evaluate(left)?;
                match token.as_logical_unchecked() {
                    Logical::Or => {
                        if Interpreter::is_truthy(&left) {
                            return Ok(left);
                        } else {
                            self.evaluate(right)
                        }
                    }
                    Logical::And => {
                        if !Interpreter::is_truthy(&left) {
                            Ok(left)
                        } else {
                            self.evaluate(right)
                        }
                    }
                }
            }
            Expr::Get(object, name) => {
                if let Some(c) = self
                    .evaluate(object)?
                    .into_callable()
                    .and_then(LoxCallable::into_instance)
                {
                    c.get(&name.lexeme)
                } else {
                    Err(RloxError::PropertyAccessOnNonInstance)
                }
            }
            Expr::Grouping(group) => self.evaluate(group),
            Expr::Variable(token) => Ok(self.look_up_variable(&token.lexeme, expr)?),
            Expr::Call(callee, _, args) => {
                // TODO figure out a better way to do this.
                //
                // We need the caller name later to update the this pointer.
                let caller_name: Option<&str> = if let Expr::Get(e, _) = callee.as_ref() {
                    if let Expr::Variable(t) = e.as_ref() {
                        Some(&t.lexeme)
                    } else {
                        None
                    }
                } else {
                    None
                };

                let function = match self.evaluate(callee)? {
                    Object::Callable(c) => match c {
                        LoxCallable::Clock
                        | LoxCallable::UserDefined(_)
                        | LoxCallable::ClassDefinition(_) => Ok(c),
                        LoxCallable::ClassInstance(_) => Err(RloxError::NotCallable),
                    },
                    _ => Err(RloxError::NotCallable),
                }?;

                if args.len() != function.arity() {
                    return Err(RloxError::ArgumentMismatch(function.arity(), args.len()));
                }

                let mut arguments = Vec::with_capacity(args.len());
                for arg in args {
                    arguments.push(self.evaluate(arg)?);
                }

                match function {
                    // TODO: handle SystemTime::now failing
                    LoxCallable::Clock => SystemTime::now()
                        .duration_since(UNIX_EPOCH)
                        .map_err(|_| unimplemented!())
                        .map(|t| Object::Time(t.as_millis())),
                    LoxCallable::UserDefined(f) => {
                        // The 'this' pointer needs to be defined in our parent environment.
                        if let Some(instance) = f.this {
                            self.environment.define(
                                THIS.to_owned(),
                                Object::Callable(LoxCallable::ClassInstance(instance)),
                            );
                        }

                        if let Some(superclass) = f.superclass {
                            self.environment.define(
                                SUPER.to_owned(),
                                Object::Callable(LoxCallable::ClassDefinition(superclass)),
                            );
                        }

                        if let Some(index) = f.environment {
                            self.environment.restore_closure(index);
                        }

                        self.environment.raise();

                        // TODO: don't clone
                        for (param, arg) in f.parameters.iter().zip(arguments.iter()) {
                            self.environment.define(param.lexeme.clone(), arg.clone())
                        }

                        let r = self.execute_block(&f.body, caller_name);
                        self.environment.restore_environment();
                        if let Err(e) = r {
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
                        } else if f.initializer {
                            self.environment.get(THIS)
                        } else {
                            Ok(Object::Nil)
                        }
                    }
                    LoxCallable::ClassDefinition(class) => {
                        let superclass = class.superclass.clone();
                        let instance = LoxInstance::new(class, superclass);
                        if let Some(LoxCallable::UserDefined(f)) = instance
                            .get(INIT_METHOD)
                            .ok()
                            .and_then(Object::into_callable)
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
                let instance_name = match object.as_ref() {
                    Expr::Variable(t) | Expr::This(t) => Ok(&t.lexeme),
                    _ => Err(RloxError::PropertyAccessOnNonInstance),
                }?;

                if let Some(mut instance) = self
                    .evaluate(object)?
                    .into_callable()
                    .and_then(LoxCallable::into_instance)
                {
                    let value = self.evaluate(value)?;
                    instance.set(&name.lexeme, value);

                    // Note: jlox relies on implicit mutation of the environment.  rlox's
                    // environment hands out copies of objects rather than references.  We need to
                    // manually update the environment after setting a field on a variable.
                    self.environment.assign(
                        &instance_name,
                        Object::Callable(LoxCallable::ClassInstance(instance.clone())),
                    )?;

                    // We just added this value. It must be `Ok`!
                    Ok(instance.get(&name.lexeme).unwrap())
                } else {
                    Err(RloxError::PropertyAccessOnNonInstance)
                }
            }
            Expr::This(keyword) => Ok(self.look_up_variable(&keyword.lexeme, expr)?),
            Expr::Super(_, method) => {
                let superclass = self
                    .look_up_variable(SUPER, expr)
                    .unwrap()
                    .into_callable_unchecked()
                    .into_definition_unchecked();

                // A 'this' pointer must exist in our environment since super is only valid in
                // a class context. The resolver guarentees that this invariant will be upheld
                // statically. It is a programming error if the 'this' pointer does not exist
                // at this point. This is not a valid runtime error.
                let this = self
                    .environment
                    .get(THIS)
                    .unwrap()
                    .into_callable_unchecked()
                    .into_instance_unchecked();

                // We need to determine if the super call is referring to a grandparent or
                // ourselves. For now, this is done by checking the existence of a superclass.
                if superclass.superclass.is_none() {
                    return this.get_super(&method.lexeme);
                } else if let Some(method) = find_method(superclass.walker(), &method.lexeme) {
                    let mut method = method.clone();
                    method.this = Some(this);
                    return Ok(Object::Callable(LoxCallable::UserDefined(method)));
                } else {
                    // TODO make new error: NoSuperMethod
                    Err(RloxError::UndefinedProperty(method.lexeme.to_owned()))
                }
            }
        }
    }

    fn look_up_variable(&mut self, name: &str, _expr: &Expr) -> Result<Object> {
        // FIXME: There's a discrepancy between the implementation of resolving
        // and storing variables in the environment at runtime. This is a hack to
        // just step through the static scopes until you find `name`.
        self.environment.get(name)
    }

    pub fn resolve(&mut self, map: HashMap<Expr, usize>) {
        self.locals.extend(map.into_iter());
    }

    // Gets the truth value of an Object.
    //
    // lox only considers false and nil falsey. Every other object variant is
    // truthy.
    pub fn is_truthy(object: &Object) -> bool {
        match object {
            Object::Nil | Object::Bool(false) => false,
            _ => true,
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        let expr = parser.parse().unwrap();
        let mut interpreter = Interpreter::new();
        assert_eq!(Ok(Object::Bool(true)), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_a_literal_expression_nil() {
        let scanner = Scanner::new("nil".to_owned());
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Nil), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_mult() {
        let scanner = Scanner::new("6 * 7".to_owned());
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Bool(true)), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_complex_equal() {
        let scanner = Scanner::new("(4 + 4) == (2 * 2 * 2)".to_owned());
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Bool(true)), interpreter.evaluate(&expr));
    }

    #[test]
    fn it_can_evaluate_string_concatenation() {
        let scanner = Scanner::new("\"foo\" + \"bar\"".to_owned());
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        let mut interpreter = Interpreter::new();
        let expr = parser.parse().unwrap();
        assert_eq!(
            Ok(Object::String(String::from("foobar"))),
            interpreter.evaluate(&expr)
        );
    }

    #[test]
    fn it_recognizes_valid_statements_print_arithmetic() {
        let scanner = Scanner::new("print 1 + 1;".to_owned());
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        assert_eq!(Err(RloxError::MissingSemicolon(1)), parser.parse_stmts());
    }

    #[test]
    fn it_supports_reassignment_block() {
        let scanner = Scanner::new("var a = 1; { a = 2; } print a;".to_owned());
        let parser = Parser::new(scanner.scan_tokens().unwrap());
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
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        let mut vec_stmts = parser.parse_stmts().unwrap();
        let mut stmts = vec_stmts.drain(..);
        let mut interpreter = Interpreter::new();
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
    }

    #[test]
    fn it_supports_empty_fun() {
        let scanner = Scanner::new("fun f() {}".to_owned());
        let parser = Parser::new(scanner.scan_tokens().unwrap());
        let mut vec_stmts = parser.parse_stmts().unwrap();
        let mut stmts = vec_stmts.drain(..);
        let mut interpreter = Interpreter::new();
        assert!(interpreter.execute(&stmts.next().unwrap()).is_ok());
    }
}
