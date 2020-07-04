use std::error;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::result;

mod interpreter;
mod parser;
mod resolver;
mod scanner;

pub type Interpreter = interpreter::Interpreter;
pub type Parser = parser::Parser;
pub type Result<T> = result::Result<T, RloxError>;
pub type Resolver = resolver::Resolver;
pub type Scanner = scanner::Scanner;

#[derive(Debug, PartialEq)]
pub enum RloxError {
    /// An internal error occured when querying for the previous element. This
    /// is either due to a programming error or an internal error in `Vec`. The
    /// former is *much* more likely.
    NoPrevious,
    /// An '(' open parenthesis token was parsed, but no ')' close parenthesis
    /// token was found.
    UnclosedParenthesis(usize),
    /// An unimplemented area as encountered. Since this interpretter is a
    /// WIP, this is a very likely error. Unfortunately, we can no longer
    /// reason about the program after receiving this error, so we must
    /// propogate it up to the caller.
    Unimplemented,
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
    /// An invalid assignment was attempted
    InvalidAssignment,
    /// An attempt was made to mutate a non unique Rc ptr
    ///
    /// Maybe this should be an assertion rather than a user facing error. This
    /// is really an implementation detail of the interpreter.
    NonUniqueRc,
    Return(Object),
    VariableRedefinition,
    ReturnInNonFunction,
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

// TODO try to make this not clone at some point.
#[derive(Clone, Debug, PartialEq)]
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

impl Eq for TokenType {}

impl Hash for TokenType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Number(f) => f.to_bits().hash(state),
            other => other.to_string().hash(state),
        }
    }
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

#[derive(Eq, Hash, Clone, Debug, PartialEq)]
pub struct Token {
    token_type: TokenType,
    lexeme: Rc<str>,
    line: usize,
}

impl Token {
    #[must_use]
    pub fn new(token_type: TokenType, lexeme: String, line: usize) -> Self {
        Token {
            token_type,
            lexeme: Rc::from(lexeme),
            line,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{} {} ", stringify!(self.token_type), self.lexeme)
    }
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
    /// The return type of Lox's native function `Time`
    Time(u128),
    Callable(LoxCallable),
}

impl Eq for Object {}

impl Hash for Object {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Number(f) => f.to_bits().hash(state),
            other => other.hash(state),
        }
    }
}

#[derive(Eq, Hash, PartialEq, Debug, Clone)]
pub enum LoxCallable {
    Clock,
    UserDefined(FunctionStmt),
}

impl LoxCallable {
    pub fn arity(&self) -> usize {
        match self {
            Self::Clock => 0,
            Self::UserDefined(f) => f.parameters.len(),
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Object::Bool(b) => write!(f, "{}", b),
            Object::Nil => write!(f, "nil"),
            Object::Number(n) => write!(f, "{}", n),
            Object::String(s) => write!(f, "{}", s),
            Object::Time(t) => write!(f, "{}", t),
            Object::Callable(c) => match c {
                LoxCallable::Clock => write!(f, "<native fn>"),
                _ => unimplemented!(),
            },
        }
    }
}

/// jlox implements this with OOP. Namely jlox:
/// - Defines an abstract class: Expr
/// - Creates a subclass for each variant (i.e. Binary, Grouping, Literal, Unary)
/// - Uses the visitor pattern to dispatch the correct method for each type.
#[derive(Eq, Hash, Debug, PartialEq, Clone)]
pub enum Expr {
    Assign(Token, Box<Expr>),
    Binary(Box<Expr>, Token, Box<Expr>),
    Call(Box<Expr>, Token, Vec<Expr>),
    Grouping(Box<Expr>),
    Literal(Object),
    Logical(Box<Expr>, Token, Box<Expr>),
    Unary(Token, Box<Expr>),
    Variable(Token),
}

// TODO: making this clone is :((
#[derive(Eq, Hash, Debug, PartialEq, Clone)]
pub struct FunctionStmt {
    name: Token,
    parameters: Vec<Token>,
    body: Vec<Stmt>,
}

#[derive(Eq, Hash, Debug, PartialEq, Clone)]
pub enum Stmt {
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Function(LoxCallable),
    Expression(Expr),
    Print(Expr),
    Return(Token, Option<Expr>),
    Var(Token, Option<Expr>),
    While(Expr, Box<Stmt>),
}
