use std::error;
use std::fmt;
use std::hash::{Hash, Hasher};
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

const INIT_METHOD: &'static str = "init";

#[derive(Debug, PartialEq)]
pub enum RloxError {
    /// An internal error occured when querying for the previous element. This
    /// is either due to a programming error or an internal error in `Vec`. The
    /// former is *much* more likely.
    NoPrevious,
    /// An '(' open parenthesis token was parsed, but no ')' close parenthesis
    /// token was found.
    UnclosedParenthesis(usize),
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
    PropertyAccessOnNonInstance,
    UndefinedProperty,
    ThisOutsideOfClass,
    ReturnValueFromConstructor,
    // expected, actual
    ArgumentMismatch(usize, usize),
    InheritFromSelf,
    InheritNonClass,
}

impl fmt::Display for RloxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Self::MismatchedOperands(op, left, right) => {
                write!(f, "error: invalid expression: {} {} {}", left, op, right)
            }
            Self::MissingSemicolon(line) => write!(f, "error: {}: missing semicolon", line),
            Self::UnclosedParenthesis(line) => write!(f, "error: {}: unclosed parenthesis", line),
            Self::ThisOutsideOfClass => {
                write!(f, "Error at 'this': Cannot use 'this' outside of a class.")
            }
            Self::ReturnValueFromConstructor => write!(
                f,
                "Error at 'return': Cannot return a value from an initializer."
            ),
            Self::ArgumentMismatch(expected, actual) => write!(
                f,
                "runtime error: Expected {} arguments but got {}.",
                expected, actual
            ),
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

    // Used when a temporary token is needed.
    Default,
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
            Self::Default => "default token; this is not a usable token",
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
    lexeme: String,
    line: usize,
}

impl Token {
    #[must_use]
    pub fn new(token_type: TokenType, lexeme: String, line: usize) -> Self {
        Token {
            token_type,
            lexeme: lexeme,
            line,
        }
    }
}

impl Default for Token {
    fn default() -> Self {
        Token {
            token_type: TokenType::Default,
            lexeme: String::new(),
            line: 0,
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
    ClassDefinition(LoxClass),
    ClassInstance(LoxInstance),
}

#[derive(Eq, Hash, PartialEq, Debug, Clone)]
pub struct LoxClass {
    name: String,
    methods: Vec<FunctionStmt>,
    superclass: Option<Box<LoxClass>>,
}

impl LoxClass {
    fn new(name: String, superclass: Option<Box<LoxClass>>) -> Self {
        LoxClass {
            name: name,
            methods: Vec::new(),
            superclass,
        }
    }

    fn add_method(&mut self, method: FunctionStmt) {
        self.methods.push(method)
    }
}

impl fmt::Display for LoxClass {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{}", self.name)
    }
}

impl LoxCallable {
    // TODO clean this up
    pub fn arity(&self) -> usize {
        match self {
            Self::Clock => 0,
            Self::UserDefined(f) => f.parameters.len(),
            // init is a bit of a strange case. If we don't find an init method on ourselves then
            // we need to look at our parent (if they exist).
            Self::ClassDefinition(d) => {
                if let Some(m) = d.methods.iter().find(|e| e.name.lexeme == INIT_METHOD) {
                    m.parameters.len()
                } else if let Some(m) = d
                    .superclass
                    .as_ref()
                    .and_then(|s| s.methods.iter().find(|e| e.name.lexeme == INIT_METHOD))
                {
                    m.parameters.len()
                } else {
                    0
                }
            }
            Self::ClassInstance(_) => 0,
        }
    }
}

#[derive(Eq, Hash, PartialEq, Debug, Clone)]
struct Property {
    name: String,
    object: Object,
}

#[derive(Eq, Hash, PartialEq, Debug, Clone)]
pub struct LoxInstance {
    // This is a copy of the name at the time of creation.
    name: String,
    // This differs from jlox since std::collections::HashMap is not Hash.
    // It might be slow.
    fields: Vec<Property>,
    methods: Vec<FunctionStmt>,
    superclass: Option<Box<LoxClass>>,
}

impl LoxInstance {
    fn new(class: LoxClass, superclass: Option<Box<LoxClass>>) -> Self {
        LoxInstance {
            name: class.name.clone(),
            fields: Vec::new(),
            methods: class.methods,
            superclass,
        }
    }

    fn get(&self, name: &str) -> Result<Object> {
        if let Some(property) = self.fields.iter().find(|e| e.name == name) {
            return Ok(property.object.clone());
        }

        if let Some(method) = self.methods.iter().find(|e| e.name.lexeme == name) {
            let mut method = method.clone();
            method.this = Some(self.clone());
            method.super_class = self.superclass.clone().map(|s| *s);
            return Ok(Object::Callable(LoxCallable::UserDefined(method)));
        } else {
            self.get_super(name)
        }
    }

    fn get_super(&self, name: &str) -> Result<Object> {
        if let Some(method) = self
            .superclass
            .as_ref()
            .map(|s| s.methods.iter().find(|e| e.name.lexeme == name))
            .flatten()
        {
            let mut method = method.clone();
            method.this = Some(self.clone());
            method.super_class = self.superclass.clone().map(|s| *s);
            Ok(Object::Callable(LoxCallable::UserDefined(method)))
        } else {
            Err(RloxError::UndefinedProperty)
        }
    }

    fn set(&mut self, name: &str, value: Object) {
        let property = Property {
            name: name.to_owned(),
            object: value,
        };

        self.fields.push(property);
    }
}

impl fmt::Display for LoxInstance {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{} instance", self.name)
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
                LoxCallable::ClassDefinition(n) => write!(f, "{}", n),
                LoxCallable::ClassInstance(n) => write!(f, "{}", n),
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
    Get(Box<Expr>, Token),
    Grouping(Box<Expr>),
    Literal(Object),
    Logical(Box<Expr>, Token, Box<Expr>),
    Set(Box<Expr>, Token, Box<Expr>),
    Super(Token, Token),
    This(Token),
    Unary(Token, Box<Expr>),
    Variable(Token),
}

// TODO: making this clone is :((
#[derive(Eq, Hash, Debug, PartialEq, Clone)]
pub struct FunctionStmt {
    name: Token,
    parameters: Vec<Token>,
    body: Vec<Stmt>,
    this: Option<LoxInstance>,
    super_class: Option<LoxClass>,
    initializer: bool,
}

#[derive(Eq, Hash, Debug, PartialEq, Clone)]
pub enum Stmt {
    Block(Vec<Stmt>),
    // TODO maybe this should be Vec of LoxCallable?
    Class(Token, Option<Expr>, Vec<Stmt>),
    Expression(Expr),
    Function(LoxCallable),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Print(Expr),
    Return(Token, Option<Expr>),
    Var(Token, Option<Expr>),
    While(Expr, Box<Stmt>),
}

#[cfg(test)]
mod tests {
    use super::*;
    mod lox_instance {
        use super::*;

        #[test]
        fn it_can_lookup_methods() {
            let method = FunctionStmt {
                name: Token::new(TokenType::Identifier, "bar".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                super_class: None,
            };

            let mut class = LoxClass::new("foo".to_owned(), None);
            class.add_method(method.clone());

            let instance = LoxInstance::new(class, None);
            let mut expected_method = method.clone();
            expected_method.this = Some(instance.clone());

            assert_eq!(
                Ok(Object::Callable(LoxCallable::UserDefined(expected_method))),
                instance.get("bar")
            );
        }

        #[test]
        fn it_fails_for_nonexistent_methods() {
            let class = LoxClass::new("foo".to_owned(), None);

            let instance = LoxInstance::new(class, None);

            assert_eq!(Err(RloxError::UndefinedProperty), instance.get("bar"));
        }

        #[test]
        fn it_can_lookup_properties() {
            let class = LoxClass::new("foo".to_owned(), None);

            let mut instance = LoxInstance::new(class, None);
            instance.set("foo", Object::String("bar".to_owned()));
            instance.set("bar", Object::String("baz".to_owned()));
            instance.set("baz", Object::String("qux".to_owned()));

            assert_eq!(Ok(Object::String("bar".to_owned())), instance.get("foo"));
            assert_eq!(Ok(Object::String("baz".to_owned())), instance.get("bar"));
            assert_eq!(Ok(Object::String("qux".to_owned())), instance.get("baz"));
        }

        #[test]
        fn it_fails_for_nonexistent_properties() {
            let class = LoxClass::new("foo".to_owned(), None);

            let instance = LoxInstance::new(class, None);

            assert_eq!(Err(RloxError::UndefinedProperty), instance.get("foo"));
            assert_eq!(Err(RloxError::UndefinedProperty), instance.get("bar"));
            assert_eq!(Err(RloxError::UndefinedProperty), instance.get("baz"));
        }
    }
}
