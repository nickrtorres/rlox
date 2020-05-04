//! `librlox` is the library that powers the rlox interpreter.
//!
//! `rlox` is a rust port of the Lox Java interpreter (i.e. `jlox`).  `rlox`
//! differs from `jlox` is a number of ways namely:
//! - `rlox` uses `std::result::Result` to report errors (`jlox` uses exceptions)
//! - `rlox` uses `Expr` and `Stmt` sum types to represent expressions and
//!   statements, respectively (`jlox` uses abstract `Expr` and `Stmt` classes and
//!   specialized subclasses).
//! - `rlox` defines associated functions for `Expr` and `Stmt` to operate on
//!   variants of each type (`jlox` uses the visitor pattern)
//! - `rlox` defines an `interpret` associated function directly on the `Expr`
//!   type (`jlox` uses a new `Interpreter` object with an `interpret` method
#![warn(clippy::pedantic)]
#![feature(str_strip)]
#![feature(bool_to_option)]
use std::cell::Cell;
use std::collections::HashMap;
use std::error;
use std::fmt;
use std::iter::Peekable;
use std::mem::discriminant;
use std::result;
use std::str::Chars;

pub type Result<T> = result::Result<T, RloxError>;

#[derive(Debug, PartialEq)]
pub enum RloxError {
    /// An internal error occured when querying for the previous element. This
    /// is either due to a programming error or an internal error in `Vec`. The
    /// former is *much* more likely.
    NoPrevious,
    /// An '(' open parenthesis token was parsed, but no ')' close parenthesis
    /// token was found.
    UnclosedParenthesis(usize),
    /// A quasi-unreachable block was reached! This is a nicer
    /// `unreachable!`---by nicer I mean it doesn't `panic`
    Unreachable,
    /// An unimplemented token was encountered. Since this interpretter is a
    /// WIP, this is a very likely error. Unfortunately, we can no longer
    /// reason about the program after receiving this error, so we must
    /// propogate it up to the caller.
    UnimplementedToken,
    /// The operand types do not match for the given binary expression. The
    /// tuple elements are in [Polish notation][wiki-NPN] i.e. operator, left, right
    ///
    /// TODO (*maybe*) mismatched operands can be specialized even further:
    /// ```notrust
    /// +--- MismatchedOperands(TokenType, Object, Object)
    /// |    - Ex:"foo" + 1
    /// |
    /// +--- InvalidOperands(TokenType, Object, Object)
    ///      - Ex: true / nil
    /// ```
    ///
    /// [wiki-NPN]: https://en.wikipedia.org/wiki/Polish_notation
    MismatchedOperands(TokenType, Object, Object),
    /// The statement entered is missing a semicolon
    MissingSemicolon(usize),
    /// A non existent variable was queried
    UndefinedVariable,
}

impl fmt::Display for RloxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Self::MismatchedOperands(op, left, right) => {
                write!(f, "error: invalid expression: {} {} {}", left, op, right)
            }
            Self::MissingSemicolon(line) => write!(f, "error: {}: missing semicolon", line),
            Self::UnclosedParenthesis(line) => write!(f, "error: {}: unclosed parenthesis", line),
            // TODO: actually handle other errors
            _ => write!(f, "{:?}", self),
        }
    }
}

impl error::Error for RloxError {}

#[derive(Debug, PartialEq)]
pub enum TokenType {
    // Single-character tokens
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals
    Identifier,
    String(String),
    Number(f64),

    // Keywords
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    Eof,
}

impl fmt::Display for TokenType {
    // Single-character tokens
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        // Handle Number separately so we don't have to allocate for the rest.
        if let Self::Number(n) = self {
            return write!(f, "{}", n);
        }

        let token = match self {
            Self::LeftParen => "(",
            Self::RightParen => ")",
            Self::LeftBrace => "{",
            Self::RightBrace => "}",
            Self::Comma => ",",
            Self::Dot => ".",
            Self::Minus => "-",
            Self::Plus => "+",
            Self::Semicolon => ";",
            Self::Slash => "/",
            Self::Star => "*",
            Self::Bang => "!",
            Self::BangEqual => "!=",
            Self::Equal => "=",
            Self::EqualEqual => "==",
            Self::Greater => ">",
            Self::GreaterEqual => ">=",
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::Identifier => "iden",
            Self::String(s) => &s,
            Self::And => "and",
            Self::Class => "class",
            Self::Else => "else",
            Self::False => "false",
            Self::Fun => "fun",
            Self::For => "for",
            Self::If => "if",
            Self::Nil => "nil",
            Self::Or => "or",
            Self::Print => "print",
            Self::Return => "return",
            Self::Super => "super",
            Self::This => "this",
            Self::True => "true",
            Self::Var => "var",
            Self::While => "while",
            Self::Eof => "eof",
            // we already handled number above
            _ => unreachable!(),
        };

        write!(f, "{}", token)
    }
}

impl TokenType {
    /// TODO rename this
    #[must_use]
    pub fn identifier_from_str(token: &str) -> TokenType {
        match token {
            "and" => TokenType::And,
            "class" => TokenType::Class,
            "else" => TokenType::Else,
            "false" => TokenType::False,
            "for" => TokenType::For,
            "fun" => TokenType::Fun,
            "if" => TokenType::If,
            "nil" => TokenType::Nil,
            "or" => TokenType::Or,
            "print" => TokenType::Print,
            "return" => TokenType::Return,
            "super" => TokenType::Super,
            "this" => TokenType::This,
            "true" => TokenType::True,
            "var" => TokenType::Var,
            "while" => TokenType::While,
            _ => TokenType::Identifier,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    token_type: TokenType,
    lexeme: String,
    line: usize,
}

impl Token {
    #[must_use]
    pub fn new(token_type: TokenType, lexeme: String, line: usize) -> Self {
        Token {
            token_type,
            lexeme,
            line,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{} {} ", stringify!(self.token_type), self.lexeme)
    }
}

pub struct Scanner<'a> {
    // Scratch pad for Tokens
    scratch: String,
    chars: Peekable<Chars<'a>>,

    // Consider making tokens, start and current Cell's to avoid
    // having to hold a mut Scanner
    tokens: Vec<Token>,
    line: usize,
}

impl<'a> Scanner<'a> {
    /// Creates a new `Scanner` whose referent is `source`.
    ///
    /// Note, a `Scanner` is only valid for the lifetime of source since a
    /// scanner is really just an encapsulated iterator over a given source
    /// `String`. Rather than having the `Scanner`s own Strings, just store a
    /// shared reference to the source input as a `Peekable<Chars>` iterator
    #[must_use]
    pub fn new(source: &'a str) -> Self {
        Scanner {
            // cautiously optimistic allocation
            scratch: String::with_capacity(1024),
            chars: source.chars().peekable(),
            tokens: Vec::new(),
            line: 1,
        }
    }

    /// Returns the list of Tokens owned by self
    pub fn scan_tokens<'s>(&'s mut self) -> &'s Vec<Token> {
        while !self.is_at_end() {
            self.scan_token();
            self.scratch.clear();
        }

        self.tokens
            .push(Token::new(TokenType::Eof, String::new(), self.line));

        &self.tokens
    }

    fn is_at_end(&mut self) -> bool {
        self.chars.peek().is_none()
    }

    fn scan_token(&mut self) {
        let c = match self.advance() {
            Some(c) => c,
            None => return,
        };

        match c {
            ' ' | '\r' | '\t' => {}
            '(' => self.add_token(TokenType::LeftParen),
            ')' => self.add_token(TokenType::RightParen),
            '{' => self.add_token(TokenType::LeftBrace),
            '}' => self.add_token(TokenType::RightBrace),
            ',' => self.add_token(TokenType::Comma),
            '.' => self.add_token(TokenType::Dot),
            '-' => self.add_token(TokenType::Minus),
            '+' => self.add_token(TokenType::Plus),
            ';' => self.add_token(TokenType::Semicolon),
            '*' => self.add_token(TokenType::Star),
            '!' => self.is_compound_equal_operator(TokenType::BangEqual, TokenType::Bang),
            '=' => self.is_compound_equal_operator(TokenType::EqualEqual, TokenType::Equal),
            '<' => self.is_compound_equal_operator(TokenType::LessEqual, TokenType::Less),
            '>' => self.is_compound_equal_operator(TokenType::GreaterEqual, TokenType::Greater),
            '/' => {
                if let Some('/') = self.peek() {
                    loop {
                        match self.advance() {
                            None | Some('\n') => break,
                            Some(_) => {}
                        }
                    }
                } else {
                    self.add_token(TokenType::Slash);
                }
            }
            '\n' => self.line += 1,
            '"' => self.string(),
            c => {
                if Scanner::is_digit(Some(c)) {
                    self.number();
                } else if c.is_alphabetic() {
                    self.identifier();
                } else {
                    eprintln!("{}: unexpected token", self.line);
                }
            }
        };
    }

    // this method has weird semantics. it feels like the right abstraction but
    // maybe it can use some work
    fn is_compound_equal_operator(&mut self, yes: TokenType, no: TokenType) {
        if let Some('=') = self.peek() {
            self.advance();
            self.add_token(yes);
        } else {
            self.add_token(no);
        };
    }

    fn identifier(&mut self) {
        while Scanner::is_alphanumeric(self.peek()) {
            self.advance();
        }

        self.add_token(TokenType::identifier_from_str(&self.scratch));
    }

    /// Adapter for Option<char>
    fn is_alphanumeric(c: Option<char>) -> bool {
        c.map_or(false, |c| c.is_ascii_alphanumeric())
    }

    /// Adapter for Option<char>
    fn is_digit(c: Option<char>) -> bool {
        c.map_or(false, |c| c.is_ascii_digit())
    }

    fn number(&mut self) {
        while Scanner::is_digit(self.peek()) {
            self.advance();
        }

        if let Some('.') = self.peek() {
            // TODO peek_next is a pain to implement since `Peekable` can only
            // step forward once. Just assume valid input for now. :(
            self.advance();

            while Scanner::is_digit(self.peek()) {
                self.advance();
            }
        }

        let value = String::from(&self.scratch);
        // TODO: danger!
        let token = TokenType::Number(value.parse::<f64>().unwrap());
        self.add_token(token);
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn string(&mut self) {
        while let Some(s) = self.advance() {
            if s == '"' {
                break;
            }
        }

        // panic: unwrapping should be safe as someone earlier
        // should catch an unterminated "
        debug_assert!(self.scratch.starts_with('\"'));
        debug_assert!(self.scratch.ends_with('\"'));
        let value = self
            .scratch
            .strip_suffix("\"")
            .and_then(|s| s.strip_prefix("\""))
            .unwrap()
            .to_string();
        self.add_token(TokenType::String(value));
    }

    fn advance(&mut self) -> Option<char> {
        self.chars.next().map(|c| {
            self.scratch.push(c);
            c
        })
    }

    fn add_token(&mut self, token: TokenType) {
        let value = String::from(&self.scratch);
        self.tokens.push(Token::new(token, value, self.line));
    }
}

/// jlox implements this with OOP. Namely jlox:
/// - Defines an abstract class: Expr
/// - Creates a subclass for each variant (i.e. Binary, Grouping, Literal, Unary)
/// - Uses the visitor pattern to dispatch the correct method for each type.
#[derive(Debug, PartialEq)]
pub enum Expr<'a> {
    Binary(Box<Expr<'a>>, &'a Token, Box<Expr<'a>>),
    Grouping(Box<Expr<'a>>),
    Literal(Object),
    Unary(&'a Token, Box<Expr<'a>>),
    Variable(&'a Token),
}

/// Emulates Java's object type for literals
///
/// The root of Java's class heirarchy is the [`Object`][java-object] class.
/// `Boolean`, `Double` (through `Number`), `String`, and others extend
/// `Object`.  This allows any Java method to return `Object` and then downcast
/// to a more specialized representation. As far as I know, there is no such
/// analogue in Rust. Instead, explicitly define an `Object` enum that offers a
/// fixed domain of acceptable types with their `Rust` primitive as the
/// underlying data.
///
/// [java-object]: https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/lang/package-tree.html
#[derive(Clone, Debug, PartialEq)]
pub enum Object {
    /// Emulates a [Java `Boolean`](https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/lang/Boolean.html)
    Bool(bool),
    /// Emulates the [*billion-dollar mistake*](https://en.wikipedia.org/wiki/Tony_Hoare#Apologies_and_retractions)
    Nil,
    /// Emulates a [Java `Double`](https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/lang/Double.html)
    Number(f64),
    /// Emulates a [Java `String`](https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/lang/String.html)
    String(String),
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Object::Bool(b) => write!(f, "{}", b),
            Object::Nil => write!(f, "nil"),
            Object::Number(n) => write!(f, "{}", n),
            Object::String(s) => write!(f, "{}", s),
        }
    }
}

pub struct Interpreter<'a> {
    environment: Environment<'a>,
}

impl<'a> Interpreter<'a> {
    pub fn new() -> Self {
        Interpreter {
            environment: Environment::new(),
        }
    }

    pub fn interpret(self, statements: Vec<Stmt>) -> Result<()> {
        for statement in statements {
            statement.execute()?;
        }

        Ok(())
    }

    fn execute(&mut self, statement: Stmt<'a>) -> Result<()> {
        match statement {
            Stmt::Expression(expr) => {
                expr.evaluate()?;
            }
            Stmt::Print(expr) => {
                let value = expr.evaluate()?;
                println!("{}", value);
            }
            Stmt::Var(token, Some(expr)) => {
                // Lifetime justification:
                // `statement` is dropped at the end of this block. However, we
                // only care about the token that `statement` has a reference to.
                // We should be fine as long as the `token` reference lives long
                // enough.
                let value = expr.evaluate()?;
                self.environment.define(&token.lexeme, value);
            }
            _ => {}
        }

        Ok(())
    }

    fn evaluate(&self, expr: Expr) -> Result<Object> {
        match expr {
            Expr::Binary(left_expr, token, right_expr) => {
                let left = self.evaluate(*left_expr)?;
                let right = self.evaluate(*right_expr)?;

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
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Number(*l + *r)),
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
                let right = self.evaluate(*expr)?;

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
            Expr::Literal(obj) => Ok(obj),
            Expr::Grouping(group) => self.evaluate(*group),
            Expr::Variable(token) => Ok(self.environment.get(token)?),
            _ => Err(RloxError::Unreachable),
        }
    }
}

impl<'a> Expr<'a> {
    fn evaluate(self) -> Result<Object> {
        match self {
            Expr::Binary(left_expr, token, right_expr) => {
                let left = left_expr.evaluate()?;
                let right = right_expr.evaluate()?;

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
                        (Object::Number(l), Object::Number(r)) => Ok(Object::Number(*l + *r)),
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
                let right = expr.evaluate()?;

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
            Expr::Literal(obj) => Ok(obj),
            Expr::Grouping(group) => group.evaluate(),
            _ => Err(RloxError::Unreachable),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Stmt<'a> {
    Expression(Expr<'a>),
    Print(Expr<'a>),
    // Variable declaration w/o assignment defaults to Option::None
    Var(&'a Token, Option<Expr<'a>>),
}

impl<'a> Stmt<'a> {
    pub fn execute(self) -> Result<()> {
        match self {
            Self::Expression(expr) => {
                expr.evaluate()?;
            }
            Self::Print(expr) => {
                let value = expr.evaluate()?;
                println!("{}", value);
            }
            Self::Var(token, Some(expr)) => {}
            _ => {}
        }

        Ok(())
    }
}

struct Environment<'a> {
    values: HashMap<&'a str, Object>,
}

impl<'a> Environment<'a> {
    fn new() -> Self {
        Environment {
            values: HashMap::new(),
        }
    }

    fn define(&mut self, name: &'a str, value: Object) {
        self.values.insert(name, value);
    }

    fn get(&self, name: &Token) -> Result<Object> {
        if let Some(lexeme) = self.values.get(name.lexeme.as_str()) {
            // TODO: The option is to clone here or put everything else on the
            // heap.  For now, cloning seems easer.
            Ok(lexeme.clone())
        } else {
            Err(RloxError::UndefinedVariable)
        }
    }
}

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
pub struct Parser<'a> {
    tokens: &'a Vec<Token>,
    /// cursor is an implementation detail end users shouldn't worry about. Use
    /// interior mutability here to avoid forcing the user to hold a mutable Parser.
    cursor: Cell<usize>,
}

impl<'a> Parser<'a> {
    #[must_use]
    pub fn new(tokens: &'a Vec<Token>) -> Self {
        Parser {
            tokens,
            cursor: Cell::new(0),
        }
    }

    pub fn parse_stmts(&self) -> Result<Vec<Stmt>> {
        let mut statements: Vec<Stmt> = Vec::new();

        while !self.is_at_end() {
            statements.push(self.declaration()?);
        }

        Ok(statements)
    }

    fn declaration(&self) -> Result<Stmt> {
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
        if self.match_tokens(vec![TokenType::Print]) {
            self.print_statement()
        } else {
            self.expression_statement()
        }
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
        self.equality()
    }

    fn equality(&'a self) -> Result<Box<Expr>> {
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

        self.primary()
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
                _ => Err(RloxError::Unreachable),
            };

            return rv;
        }

        if self.match_tokens(vec![TokenType::Identifier]) {
            return Ok(Box::new(Expr::Variable(self.previous()?)));
        }

        if self.match_tokens(vec![TokenType::LeftParen]) {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen)?;
            return Ok(Box::new(Expr::Grouping(expr)));
        }

        Err(RloxError::UnimplementedToken)
    }

    fn consume(&self, token_type: TokenType) -> Result<&Token> {
        if !self.check(&token_type) {
            // We already consumed the problematic token.  We need to step back
            // for a second to grab the bad line number. It should be *impossible*
            // for the token we just consumed to not be there.
            let line = self.previous().map_err(|_| RloxError::Unreachable)?.line;

            match token_type {
                TokenType::RightParen => return Err(RloxError::UnclosedParenthesis(line)),
                TokenType::Semicolon => return Err(RloxError::MissingSemicolon(line)),
                _ => return Err(RloxError::Unreachable),
            }
        }

        // We just validated the next token. It must exist.
        self.advance().ok_or(RloxError::Unreachable)
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

    fn previous(&self) -> Result<&Token> {
        debug_assert!(self.cursor.get() > 0);
        self.tokens
            .get(self.cursor.get() - 1)
            .ok_or(RloxError::NoPrevious)
    }

    fn advance(&self) -> Option<&Token> {
        if !self.is_at_end() {
            let old = self.cursor.get();
            self.cursor.replace(old + 1);
        }

        self.previous().ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_can_advance_through_stream() {
        let mut scanner = Scanner::new("true;");
        assert_eq!(Some('t'), scanner.advance());
        assert_eq!(Some('r'), scanner.advance());
        assert_eq!(Some('u'), scanner.advance());
        assert_eq!(Some('e'), scanner.advance());
        assert_eq!(Some(';'), scanner.advance());
        assert_eq!(None, scanner.advance());
        assert_eq!(None, scanner.advance());
    }

    #[test]
    fn it_can_peek_without_advancing() {
        let mut scanner = Scanner::new("true;");
        assert_eq!(Some('t'), scanner.advance());
        assert_eq!(Some('r'), scanner.peek());
        assert_eq!(Some('r'), scanner.advance());
        assert_eq!(Some('u'), scanner.peek());
        assert_eq!(Some('u'), scanner.advance());
        assert_eq!(Some('e'), scanner.peek());
        assert_eq!(Some('e'), scanner.advance());
        assert_eq!(Some(';'), scanner.peek());
        assert_eq!(Some(';'), scanner.advance());
        assert_eq!(None, scanner.peek());
        assert_eq!(None, scanner.advance());
    }

    // TODO: This test reaches into the guts of Scanner a bit more than I'd like.
    #[test]
    fn it_can_scan_a_boolean_token() {
        let mut scanner = Scanner::new("true");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());
    }

    // Induction: assumes all reserved words work the same
    #[test]
    fn it_can_scan_a_reserved_word() {
        let mut scanner = Scanner::new("return");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(TokenType::Return, String::from("return"), 1);
        assert_eq!(t, Some(&expected));
    }

    #[test]
    fn it_can_scan_a_non_reserved_word() {
        let mut scanner = Scanner::new("foobar");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(TokenType::Identifier, String::from("foobar"), 1);
        assert_eq!(t, Some(&expected));
    }

    // Induction: assumes all single character tokens work the same
    #[test]
    fn it_can_scan_a_single_character_token() {
        let mut scanner = Scanner::new("(");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(TokenType::LeftParen, String::from("("), 1);
        assert_eq!(t, Some(&expected));
    }

    // Induction: assumes all dual character tokens work the same
    #[test]
    fn it_can_scan_a_dual_character_token() {
        let mut scanner = Scanner::new("!=");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(TokenType::BangEqual, String::from("!="), 1);
        assert_eq!(t, Some(&expected));
    }

    #[test]
    fn it_ignores_comments() {
        let mut scanner = Scanner::new("//");
        scanner.scan_token();
        assert_eq!(0, scanner.tokens.len());
    }

    #[test]
    fn it_scans_literal_slashes() {
        let mut scanner = Scanner::new("/");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(TokenType::Slash, String::from("/"), 1);
        assert_eq!(t, Some(&expected));
    }

    #[test]
    fn it_increments_linecount() {
        let mut scanner = Scanner::new("\n");
        let line = scanner.line;
        scanner.scan_token();
        assert_eq!(line + 1, scanner.line);
    }

    // Induction: assumes it works for all don't cares
    #[test]
    fn it_ignores_dont_care_tokens() {
        let mut scanner = Scanner::new("\t");
        scanner.scan_token();
        assert_eq!(0, scanner.tokens.len());
    }

    #[test]
    fn it_can_scan_string_literals() {
        let mut scanner = Scanner::new("\"foo\"");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(
            TokenType::String(String::from("foo")),
            String::from("\"foo\""),
            1,
        );
        assert_eq!(t, Some(&expected));
    }

    #[test]
    fn it_can_scan_integers() {
        let mut scanner = Scanner::new("42");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(TokenType::Number(42 as f64), String::from("42"), 1);
        assert_eq!(t, Some(&expected));
    }

    #[test]
    fn it_can_scan_floating_point_numbers() {
        let mut scanner = Scanner::new("3.14");
        scanner.scan_token();
        assert_eq!(1, scanner.tokens.len());

        let t = scanner.tokens.first();
        let expected = Token::new(TokenType::Number(3.14), String::from("3.14"), 1);
        assert_eq!(t, Some(&expected));
    }

    #[test]
    fn it_can_scan_numerous_tokens_expression() {
        let mut scanner = Scanner::new("var breakfast;");
        let actual = scanner.scan_tokens();
        // 'var' , 'breakfast' , ';' , 'EOF'
        assert_eq!(4, actual.len());

        let expected = vec![
            Token::new(TokenType::Var, String::from("var"), 1),
            Token::new(TokenType::Identifier, String::from("breakfast"), 1),
            Token::new(TokenType::Semicolon, String::from(";"), 1),
            Token::new(TokenType::Eof, String::from(""), 1),
        ];

        for i in 0..4 {
            assert_eq!(actual.get(i), expected.get(i));
        }
    }

    #[test]
    fn it_can_scan_numerous_tokens_assignment() {
        let mut scanner = Scanner::new("var breakfast = \"bagels\";");
        let actual = scanner.scan_tokens();
        // 'var' , 'breakfast' , '=' , 'bagels' , ';' , 'EOF'
        assert_eq!(6, actual.len());

        let expected = vec![
            Token::new(TokenType::Var, String::from("var"), 1),
            Token::new(TokenType::Identifier, String::from("breakfast"), 1),
            Token::new(TokenType::Equal, String::from("="), 1),
            Token::new(
                TokenType::String(String::from("bagels")),
                String::from("\"bagels\""),
                1,
            ),
            Token::new(TokenType::Semicolon, String::from(";"), 1),
            Token::new(TokenType::Eof, String::from(""), 1),
        ];

        for i in 0..6 {
            assert_eq!(actual.get(i), expected.get(i));
        }
    }

    #[test]
    fn it_can_scan_numerous_tokens_conditional_with_newlines() {
        let mut scanner =
            Scanner::new("if (condition) {\n  print \"yes\";\n} else {\n  print \"no\";\n}\n");
        let actual = scanner.scan_tokens();
        // 'if' , '(' , 'condition' , ')' , '{' , 'print' , 'yes' , ';' , '}' , 'else' , '{' ,
        // 'print' , 'no' , ';' , '}' , 'EOF'
        assert_eq!(16, actual.len());
        let expected = vec![
            Token::new(TokenType::If, String::from("if"), 1),
            Token::new(TokenType::LeftParen, String::from("("), 1),
            Token::new(TokenType::Identifier, String::from("condition"), 1),
            Token::new(TokenType::RightParen, String::from(")"), 1),
            Token::new(TokenType::LeftBrace, String::from("{"), 1),
            Token::new(TokenType::Print, String::from("print"), 2),
            Token::new(
                TokenType::String(String::from("yes")),
                String::from("\"yes\""),
                2,
            ),
            Token::new(TokenType::Semicolon, String::from(";"), 2),
            Token::new(TokenType::RightBrace, String::from("}"), 3),
            Token::new(TokenType::Else, String::from("else"), 3),
            Token::new(TokenType::LeftBrace, String::from("{"), 3),
            Token::new(TokenType::Print, String::from("print"), 4),
            Token::new(
                TokenType::String(String::from("no")),
                String::from("\"no\""),
                4,
            ),
            Token::new(TokenType::Semicolon, String::from(";"), 4),
            Token::new(TokenType::RightBrace, String::from("}"), 5),
            Token::new(TokenType::Eof, String::from(""), 6),
        ];

        for i in 0..16 {
            assert_eq!(actual.get(i), expected.get(i));
        }
    }

    #[test]
    fn it_can_advance_over_token_iterator() {
        let mut scanner = Scanner::new("var breakfast;");
        let parser = Parser::new(scanner.scan_tokens());

        assert_eq!(
            Some(&Token::new(TokenType::Var, String::from("var"), 1)),
            parser.advance()
        );
        assert_eq!(
            Some(&Token::new(
                TokenType::Identifier,
                String::from("breakfast"),
                1
            )),
            parser.advance()
        );
        assert_eq!(
            Some(&Token::new(TokenType::Semicolon, String::from(";"), 1)),
            parser.advance()
        );

        assert_eq!(
            Some(&Token::new(TokenType::Semicolon, String::from(";"), 1)),
            parser.advance()
        );
    }

    #[test]
    fn it_can_parse_a_float() {
        let mut scanner = Scanner::new("1");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Literal(Object::Number(1 as f64)),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_bool() {
        let mut scanner = Scanner::new("true");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Expr::Literal(Object::Bool(true)), *parser.parse().unwrap());
    }

    #[test]
    fn it_can_parse_nil() {
        let mut scanner = Scanner::new("nil");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Expr::Literal(Object::Nil), *parser.parse().unwrap());
    }

    #[test]
    fn it_can_parse_a_unary_expression() {
        let mut scanner = Scanner::new("-1");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Unary(
                &Token::new(TokenType::Minus, "-".to_owned(), 1),
                Box::new(Expr::Literal(Object::Number(1 as f64)))
            ),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_binary_expression() {
        let mut scanner = Scanner::new("1 + 2");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Binary(
                Box::new(Expr::Literal(Object::Number(1 as f64))),
                &Token::new(TokenType::Plus, "+".to_owned(), 1),
                Box::new(Expr::Literal(Object::Number(2 as f64)))
            ),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_grouping_expression() {
        let mut scanner = Scanner::new("(1)");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(
            Expr::Grouping(Box::new(Expr::Literal(Object::Number(1 as f64)))),
            *parser.parse().unwrap()
        );
    }

    #[test]
    fn it_can_parse_a_compound_expression() {
        let mut scanner = Scanner::new("(1 + 2) * 3");
        let parser = Parser::new(scanner.scan_tokens());

        let plus = Token::new(TokenType::Plus, "+".to_owned(), 1);
        let add_expr = Expr::Grouping(Box::new(Expr::Binary(
            Box::new(Expr::Literal(Object::Number(1 as f64))),
            &plus,
            Box::new(Expr::Literal(Object::Number(2 as f64))),
        )));

        let star = Token::new(TokenType::Star, "*".to_owned(), 1);
        let expected = Expr::Binary(
            Box::new(add_expr),
            &star,
            Box::new(Expr::Literal(Object::Number(3 as f64))),
        );

        assert_eq!(expected, *parser.parse().unwrap());
    }

    #[test]
    fn it_can_parse_an_arbitrarily_complex_expression() {
        let mut scanner = Scanner::new("(1 + 2) * 3 > (4 - 5) / 6");
        let parser = Parser::new(scanner.scan_tokens());

        let plus = Token::new(TokenType::Plus, "+".to_owned(), 1);
        let add_expr = Expr::Grouping(Box::new(Expr::Binary(
            Box::new(Expr::Literal(Object::Number(1 as f64))),
            &plus,
            Box::new(Expr::Literal(Object::Number(2 as f64))),
        )));

        let star = Token::new(TokenType::Star, "*".to_owned(), 1);
        let star_expr = Expr::Binary(
            Box::new(add_expr),
            &star,
            Box::new(Expr::Literal(Object::Number(3 as f64))),
        );

        let minus = Token::new(TokenType::Minus, "-".to_owned(), 1);
        let sub_expr = Expr::Grouping(Box::new(Expr::Binary(
            Box::new(Expr::Literal(Object::Number(4 as f64))),
            &minus,
            Box::new(Expr::Literal(Object::Number(5 as f64))),
        )));

        let slash = Token::new(TokenType::Slash, "/".to_owned(), 1);
        let slash_expr = Expr::Binary(
            Box::new(sub_expr),
            &slash,
            Box::new(Expr::Literal(Object::Number(6 as f64))),
        );

        let greater = Token::new(TokenType::Greater, ">".to_owned(), 1);
        let expected = Expr::Binary(Box::new(star_expr), &greater, Box::new(slash_expr));

        assert_eq!(expected, *parser.parse().unwrap());
    }

    #[test]
    fn it_detects_unclosed_parenthesis() {
        let mut scanner = Scanner::new("(1");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Err(RloxError::UnclosedParenthesis(1)), parser.parse());
    }

    #[test]
    fn it_is_a_wip() {
        let mut scanner = Scanner::new("var foo = \"bar\";");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Err(RloxError::UnimplementedToken), parser.parse());
    }

    #[test]
    fn it_can_evaluate_a_unary_expression() {
        let mut scanner = Scanner::new("-1");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Number(f64::from(-1))), expr.evaluate());
    }

    #[test]
    fn it_can_evaluate_a_literal_expression() {
        let mut scanner = Scanner::new("true");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Bool(true)), expr.evaluate());
    }

    #[test]
    fn it_can_evaluate_a_literal_expression_nil() {
        let mut scanner = Scanner::new("nil");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Nil), expr.evaluate());
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_mult() {
        let mut scanner = Scanner::new("6 * 7");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Number(f64::from(42))), expr.evaluate());
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_div() {
        let mut scanner = Scanner::new("8 / 4");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Number(f64::from(8 / 4))), expr.evaluate());
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_complex_notequal() {
        let mut scanner = Scanner::new("2 * 3 - 4 != 5 * 6 - 7");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Bool(true)), expr.evaluate());
    }

    #[test]
    fn it_can_evaluate_a_binary_expression_complex_equal() {
        let mut scanner = Scanner::new("(4 + 4) == (2 * 2 * 2)");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::Bool(true)), expr.evaluate());
    }

    #[test]
    fn it_can_evaluate_string_concatenation() {
        let mut scanner = Scanner::new("\"foo\" + \"bar\"");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(Ok(Object::String(String::from("foobar"))), expr.evaluate());
    }

    #[test]
    fn it_identifies_mismatched_operands_plus() {
        let mut scanner = Scanner::new("1 + \"foo\"");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Plus,
                Object::Number(f64::from(1)),
                Object::String("foo".to_owned())
            )),
            expr.evaluate()
        );
    }

    #[test]
    fn it_identifies_mismatched_operands_minus() {
        let mut scanner = Scanner::new("1 - \"bar\"");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Minus,
                Object::Number(f64::from(1)),
                Object::String("bar".to_owned())
            )),
            expr.evaluate()
        );
    }

    #[test]
    fn it_identifies_mismatched_operands_star() {
        let mut scanner = Scanner::new("true * 1");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Star,
                Object::Bool(true),
                Object::Number(f64::from(1)),
            )),
            expr.evaluate()
        );
    }

    #[test]
    fn it_identifies_mismatched_operands_slash() {
        let mut scanner = Scanner::new("1 / nil");
        let parser = Parser::new(scanner.scan_tokens());
        let expr = parser.parse().unwrap();
        assert_eq!(
            Err(RloxError::MismatchedOperands(
                TokenType::Slash,
                Object::Number(f64::from(1)),
                Object::Nil
            )),
            expr.evaluate()
        );
    }

    #[test]
    fn it_recognizes_valid_statements_print_arithmetic() {
        let mut scanner = Scanner::new("print 1 + 1;");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_valid_statements_print_boolean() {
        let mut scanner = Scanner::new("print true;");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_valid_statements_print_string() {
        let mut scanner = Scanner::new("print \"foo\";");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_valid_statements_print_nil() {
        let mut scanner = Scanner::new("print nil;");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_valid_statements_expression_arithmetic() {
        let mut scanner = Scanner::new("1 + 1;");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_valid_statements_expression_boolean() {
        let mut scanner = Scanner::new("true;");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_valid_statements_expression_string() {
        let mut scanner = Scanner::new("\"foo\";");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_valid_statements_expression_nil() {
        let mut scanner = Scanner::new("nil;");
        let parser = Parser::new(scanner.scan_tokens());
        let mut statements = parser.parse_stmts().unwrap();

        assert_eq!(statements.len(), 1);
        // TODO yikes
        assert_eq!(Ok(()), statements.drain(..).next().unwrap().execute());
    }

    #[test]
    fn it_recognizes_invalid_statements_missing_semicolon() {
        let mut scanner = Scanner::new("print nil");
        let parser = Parser::new(scanner.scan_tokens());
        assert_eq!(Err(RloxError::MissingSemicolon(1)), parser.parse_stmts());
    }
}
