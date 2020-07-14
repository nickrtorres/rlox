use std::error;
use std::hash::{Hash, Hasher};
use std::num::ParseFloatError;
use std::result;

mod display;
pub mod interpreter;
pub mod parser;
pub mod resolver;
pub mod scanner;

pub type Interpreter = interpreter::Interpreter;
pub type Parser = parser::Parser;
pub type Result<T> = result::Result<T, RloxError>;
pub type Resolver = resolver::Resolver;
pub type Scanner = scanner::Scanner;

const INIT_METHOD: &str = "init";
const MAX_PARAMS: usize = 255;

#[derive(Debug, PartialEq)]
pub enum RloxError {
    // expected, actual
    ArgumentMismatch(usize, usize),
    ExpectedExpression(Token),
    ExpectedVarName(Token),
    FloatParseError(usize, ParseFloatError),
    InheritFromSelf(String),
    InheritNonClass,
    InvalidAssignment,
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
    NotCallable,
    PropertyAccessOnNonInstance,
    Return(Object),
    ReturnInNonFunction,
    ReturnValueFromConstructor,
    SuperOutsideOfClass(Token),
    SuperWithoutParent(Token),
    ThisOutsideOfClass,
    TooManyArgs(Token),
    /// An '(' open parenthesis token was parsed, but no ')' close parenthesis
    /// token was found.
    UnclosedParenthesis(usize),
    UndefinedProperty(String),
    /// A non existent variable was queried
    UndefinedVariable(String),
    // expected, actual, previous
    UnexpectedToken(String, Token, Token),
    UnterminatedString(usize),
    VariableRedefinition,
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

impl Eq for TokenType {}

impl Hash for TokenType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Number(f) => f.to_bits().hash(state),
            other => other.to_string().hash(state),
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
            lexeme,
            line,
        }
    }
}

impl Default for Token {
    #[must_use]
    fn default() -> Self {
        Token {
            token_type: TokenType::Default,
            lexeme: String::new(),
            line: 0,
        }
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
    /// Emulates a [Java Callable](https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/util/concurrent/Callable.html)
    Callable(LoxCallable),
    /// Emulates the [*billion-dollar mistake*](https://en.wikipedia.org/wiki/Tony_Hoare#Apologies_and_retractions)
    Nil,
    /// Emulates a [Java `Double`](https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/lang/Double.html)
    Number(f64),
    /// Emulates a [Java `String`](https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/lang/String.html)
    String(String),
    /// The return type of Lox's native function `Time`
    Time(u128),
}

impl Eq for Object {}

impl Hash for Object {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Bool(b) => b.hash(state),
            Self::Callable(c) => c.hash(state),
            Self::Number(f) => f.to_bits().hash(state),
            Self::String(s) => s.hash(state),
            Self::Time(t) => t.hash(state),
            Self::Nil => self.hash(state),
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

impl LoxCallable {
    // TODO clean this up
    #[must_use]
    pub fn arity(&self) -> usize {
        match self {
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
            Self::Clock | Self::ClassInstance(_) => 0,
        }
    }
}

#[derive(Eq, Hash, PartialEq, Debug, Clone)]
pub struct LoxClass {
    name: String,
    methods: Vec<FunctionStmt>,
    superclass: Option<Box<LoxClass>>,
}

impl LoxClass {
    #[must_use]
    fn new(name: String, superclass: Option<Box<LoxClass>>) -> Self {
        LoxClass {
            name,
            methods: Vec::default(),
            superclass,
        }
    }

    fn add_method(&mut self, method: FunctionStmt) {
        self.methods.push(method)
    }

    #[must_use]
    fn walker(&self) -> LoxClassWalker {
        LoxClassWalker {
            superclass: self.superclass.as_ref().map(|s| &**s),
        }
    }
}

pub struct LoxClassWalker<'a> {
    superclass: Option<&'a LoxClass>,
}

impl<'a> LoxClassWalker<'a> {
    fn new(superclass: Option<&'a LoxClass>) -> Self {
        LoxClassWalker { superclass }
    }
}

pub trait Walk<'a> {
    fn walk(&mut self) -> Option<&'a LoxClass>;
}

impl<'a> Walk<'a> for LoxClassWalker<'a> {
    fn walk(&mut self) -> Option<&'a LoxClass> {
        let data = self.superclass;
        self.superclass = self
            .superclass
            .and_then(|outer| outer.superclass.as_ref().map(|inner| &**inner));
        data
    }
}

impl<'a> Iterator for LoxClassWalker<'a> {
    type Item = &'a LoxClass;

    fn next(&mut self) -> Option<Self::Item> {
        self.walk()
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
    #[must_use]
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
            method.superclass = self.superclass.clone().map(|s| *s);
            Ok(Object::Callable(LoxCallable::UserDefined(method)))
        } else {
            self.get_super(name)
        }
    }

    /// Searches for `name` in `self`'s inheritance tree
    ///
    /// A super method can be be arbitrarily nested. We need to walk the
    /// superclass list until we (1) find the method we're looking for or (2)
    /// exhaust the candidate list.
    fn get_super(&self, name: &str) -> Result<Object> {
        for candidate in self.walker() {
            if let Some(method) = candidate.methods.iter().find(|e| e.name.lexeme == name) {
                let mut method = method.clone();
                method.this = Some(self.clone());
                method.superclass = self.superclass.clone().map(|s| *s);
                return Ok(Object::Callable(LoxCallable::UserDefined(method)));
            }
        }

        Err(RloxError::UndefinedProperty(name.to_owned()))
    }

    fn set(&mut self, name: &str, value: Object) {
        let property = Property {
            name: name.to_owned(),
            object: value,
        };

        // TODO This should probably be a hash set and use the entry API.
        match self.fields.iter_mut().find(|v| v.name == name) {
            Some(e) => *e = property,
            None => self.fields.push(property),
        };
    }

    fn walker(&self) -> LoxClassWalker {
        LoxClassWalker::new(self.superclass.as_ref().map(|s| &**s))
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
    superclass: Option<LoxClass>,
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
                superclass: None,
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

            assert_eq!(
                Err(RloxError::UndefinedProperty("bar".to_owned())),
                instance.get("bar")
            );
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

            assert_eq!(
                Err(RloxError::UndefinedProperty("foo".to_owned())),
                instance.get("foo")
            );
            assert_eq!(
                Err(RloxError::UndefinedProperty("bar".to_owned())),
                instance.get("bar")
            );
            assert_eq!(
                Err(RloxError::UndefinedProperty("baz".to_owned())),
                instance.get("baz")
            );
        }

        #[test]
        fn it_can_walk_the_inheritance_tree() {
            // Emulates the inheritance tree:
            //
            // class Base {
            //   f() {}
            // }
            //
            // class Derived < Base {}
            //
            let mut base = LoxClass::new("base".to_owned(), None);
            let mut method = FunctionStmt {
                name: Token::new(TokenType::Identifier, "f".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                superclass: None,
            };
            base.add_method(method.clone());

            let derived = LoxClass::new("derived".to_owned(), Some(Box::new(base.clone())));

            let instance = LoxInstance::new(derived, Some(Box::new(base.clone())));
            method.this = Some(instance.clone());
            method.superclass = Some(base);

            assert_eq!(
                Ok(Object::Callable(LoxCallable::UserDefined(method))),
                instance.get("f")
            );
        }

        #[test]
        fn it_can_walk_the_inheritance_tree_indirect() {
            // Emulates the inheritance tree:
            //
            // class Base {
            //   f() {}
            // }
            //
            // class Indirect < Base {}
            //
            // class Derived < Indirect {}
            //
            let mut base = LoxClass::new("base".to_owned(), None);
            let mut method = FunctionStmt {
                name: Token::new(TokenType::Identifier, "f".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                superclass: None,
            };
            base.add_method(method.clone());

            let indirect = LoxClass::new("indirect".to_owned(), Some(Box::new(base.clone())));
            let derived = LoxClass::new("derived".to_owned(), Some(Box::new(indirect.clone())));

            let instance = LoxInstance::new(derived, Some(Box::new(indirect.clone())));
            method.this = Some(instance.clone());
            method.superclass = Some(indirect);

            assert_eq!(
                Ok(Object::Callable(LoxCallable::UserDefined(method))),
                instance.get("f")
            );
        }

        #[test]
        fn it_can_walk_the_inheritance_tree_very_indirect() {
            // Emulates the inheritance tree:
            //
            // class Base {
            //   f() {}
            // }
            //
            // class IndirectOne < Base {}
            //
            // class IndirectTwo < IndirectOne {}
            //
            // class Derived < IndirectTwo {}
            //
            let mut base = LoxClass::new("base".to_owned(), None);
            let mut method = FunctionStmt {
                name: Token::new(TokenType::Identifier, "f".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                superclass: None,
            };
            base.add_method(method.clone());

            let indirect_one =
                LoxClass::new("indirect_one".to_owned(), Some(Box::new(base.clone())));
            let indirect_two = LoxClass::new(
                "indirect_two".to_owned(),
                Some(Box::new(indirect_one.clone())),
            );
            let derived = LoxClass::new("derived".to_owned(), Some(Box::new(indirect_two.clone())));

            let instance = LoxInstance::new(derived, Some(Box::new(indirect_two.clone())));
            method.this = Some(instance.clone());
            method.superclass = Some(indirect_two);

            assert_eq!(
                Ok(Object::Callable(LoxCallable::UserDefined(method))),
                instance.get("f")
            );
        }
    }
    mod walker {
        use super::*;

        #[test]
        fn it_can_walk_an_inheritance_tree() {
            let grandparent = LoxClass::new("grandparent".to_owned(), None);
            let parent = LoxClass::new("parent".to_owned(), Some(Box::new(grandparent.clone())));
            let child = LoxClass::new("child".to_owned(), Some(Box::new(parent.clone())));

            let mut walker = LoxClassWalker::new(child.superclass.as_ref().map(|s| &**s));

            assert_eq!(Some(&parent), walker.walk());
            assert_eq!(Some(&grandparent), walker.walk());
            assert_eq!(None, walker.walk());
        }

        #[test]
        fn it_is_iterable() {
            let grandparent = LoxClass::new("grandparent".to_owned(), None);
            let parent = LoxClass::new("parent".to_owned(), Some(Box::new(grandparent.clone())));
            let child = LoxClass::new("child".to_owned(), Some(Box::new(parent.clone())));

            let ancestors: Vec<&LoxClass> =
                LoxClassWalker::new(child.superclass.as_ref().map(|s| &**s)).collect();

            assert_eq!(vec![&parent, &grandparent], ancestors);
        }
    }
}
