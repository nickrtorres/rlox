use std::error;
use std::hash::{Hash, Hasher};
use std::num::ParseFloatError;
use std::ops::{Add, Div, Mul, Sub};
use std::result;

mod display;
pub mod environment;
pub mod interpreter;
pub mod parser;
pub mod resolver;
pub mod scanner;

type Environment = environment::Environment;
pub type Interpreter = interpreter::Interpreter;
pub type Parser = parser::Parser;
pub type Result<T> = result::Result<T, RloxError>;
pub type Resolver = resolver::Resolver;
pub type Scanner = scanner::Scanner;

const INIT_METHOD: &str = "init";
const MAX_PARAMS: usize = 255;

#[derive(Debug, PartialEq)]
pub enum ArithmeticOperation {
    Addition,
    Subtraction,
    Multiplication,
    Negate,
    Division,
}

#[derive(Debug, PartialEq)]
pub enum RloxError {
    // expected, actual
    ArgumentMismatch(usize, usize),
    BadArithmeticOperation(ArithmeticOperation),
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

pub enum Logical {
    And,
    Or,
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

    pub fn as_logical_unchecked(&self) -> Logical {
        match self.token_type {
            TokenType::And => Logical::And,
            TokenType::Or => Logical::Or,
            _ => panic!("unsupported variant!"),
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

impl Object {
    /// Destructures an `Object` into a `LoxCallable`
    ///
    /// # Returns
    /// Returns `Some(LoxCallable)` if `self` holds a Callable variant. Returns
    /// `None` otherwise.
    pub fn into_callable(self) -> Option<LoxCallable> {
        match self {
            Self::Callable(c) => Some(c),
            _ => None,
        }
    }

    /// Destructures an `Object` into a `LoxCallable`
    ///
    /// # Panics
    /// Panics if `self` does not hold a `Callable` variant.
    pub fn into_callable_unchecked(self) -> LoxCallable {
        match self {
            Self::Callable(c) => c,
            _ => panic!("attempted to get a callable from a non-callable variant"),
        }
    }

    /// Destructures an `Object` into an `Some(f64)`
    ///
    /// Returns `Some(f64)` if `self` holds a `Number` variant. Returns
    /// `None` otherwise.
    pub fn into_number(self) -> Option<f64> {
        match self {
            Self::Number(n) => Some(n),
            _ => None,
        }
    }
}

impl Add<Object> for Object {
    type Output = Result<Object>;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (Object::Time(l), Object::Time(r)) => Ok(Object::Time(l - r)),
            (Object::Number(l), Object::Number(r)) => Ok(Object::Number(f64::from(l + r))),
            (Object::String(ref l), Object::String(ref r)) => {
                let mut buffer = String::with_capacity(l.capacity() + r.capacity());
                buffer.push_str(l);
                buffer.push_str(r);
                Ok(Object::String(buffer))
            }
            _ => Err(RloxError::BadArithmeticOperation(
                ArithmeticOperation::Addition,
            )),
        }
    }
}

impl Mul<Object> for Object {
    type Output = Result<Object>;

    fn mul(self, other: Self) -> Self::Output {
        match (self, other) {
            (Object::Number(l), Object::Number(r)) => Ok(Object::Number(f64::from(l * r))),
            _ => Err(RloxError::BadArithmeticOperation(
                ArithmeticOperation::Multiplication,
            )),
        }
    }
}

impl Div<Object> for Object {
    type Output = Result<Object>;

    fn div(self, other: Self) -> Self::Output {
        match (self, other) {
            (Object::Number(l), Object::Number(r)) => Ok(Object::Number(f64::from(l / r))),
            _ => Err(RloxError::BadArithmeticOperation(
                ArithmeticOperation::Division,
            )),
        }
    }
}

impl Sub<Object> for Object {
    type Output = Result<Object>;

    fn sub(self, other: Self) -> Self::Output {
        match (self, other) {
            (Object::Time(l), Object::Time(r)) => Ok(Object::Time(l - r)),
            (Object::Number(l), Object::Number(r)) => Ok(Object::Number(f64::from(l - r))),
            _ => Err(RloxError::BadArithmeticOperation(
                ArithmeticOperation::Subtraction,
            )),
        }
    }
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
    UserDefined(LoxFunction),
    ClassDefinition(LoxClass),
    ClassInstance(LoxInstance),
}

impl LoxCallable {
    /// Returns the arity of a `LoxCallable`
    #[must_use]
    pub fn arity(&self) -> usize {
        match self {
            Self::UserDefined(f) => f.parameters.len(),
            Self::ClassDefinition(class) => {
                find_method(LoxClassWalker::new(Some(class)), INIT_METHOD)
                    .map_or(0, |m| m.parameters.len())
            }
            Self::Clock | Self::ClassInstance(_) => 0,
        }
    }

    /// Destructures a `LoxCallable` into a `LoxInstance`
    ///
    /// # Returns
    /// `Some(LoxInstance)` if `self` holds a `ClassInstance` variant. Returns
    /// `None` otherwise.
    pub fn into_instance(self) -> Option<LoxInstance> {
        match self {
            Self::ClassInstance(c) => Some(c),
            _ => None,
        }
    }

    /// Destructures a `LoxCallable` into a `LoxInstance`
    ///
    /// # Panics
    /// Panics if `self` does not hold a [`ClassInstance`] variant.
    ///
    /// [`ClassInstance`]: #variant.ClassInstance
    pub fn into_instance_unchecked(self) -> LoxInstance {
        match self {
            Self::ClassInstance(c) => c,
            _ => panic!("attempted to get an instance from a non-instance variant"),
        }
    }

    /// Destructures a `LoxCallable` into a `LoxClass`
    ///
    /// # Returns
    /// `Some(LoxClass)` if `self` holds a `ClassDefinition` variant. Returns
    /// `None` otherwise.
    fn into_definition(self) -> Option<LoxClass> {
        match self {
            Self::ClassDefinition(d) => Some(d),
            _ => None,
        }
    }

    /// Destructures a `LoxCallable` into a `LoxClass`
    ///
    /// # Panics
    /// Panics if `self` does not hold a `ClassDefinition` variant.
    pub fn into_definition_unchecked(self) -> LoxClass {
        match self {
            Self::ClassDefinition(d) => d,
            _ => panic!("attempted to get an definition from a non-definition variant"),
        }
    }
}

#[derive(Eq, Hash, PartialEq, Debug, Clone)]
pub struct LoxClass {
    name: String,
    methods: Vec<LoxFunction>,
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

    fn add_method(&mut self, method: LoxFunction) {
        self.methods.push(method)
    }

    #[must_use]
    fn walker(&self) -> LoxClassWalker {
        LoxClassWalker::new(self.superclass.as_deref())
    }
}

pub struct LoxClassWalker<'a> {
    current: Option<&'a LoxClass>,
}

impl<'a> LoxClassWalker<'a> {
    fn new(current: Option<&'a LoxClass>) -> Self {
        LoxClassWalker { current }
    }
}

pub trait Walk<'a> {
    type Item;
    fn walk(&mut self) -> Option<Self::Item>;
}

impl<'a> Walk<'a> for LoxClassWalker<'a> {
    type Item = &'a LoxClass;
    fn walk(&mut self) -> Option<Self::Item> {
        let data = self.current;
        self.current = self.current.and_then(|outer| outer.superclass.as_deref());
        data
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
    methods: Vec<LoxFunction>,
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
        find_method(self.walker(), name)
            .map(|method| {
                let mut method = method.clone();
                method.this = Some(self.clone());
                method.superclass = self.superclass.clone().map(|s| *s);
                Object::Callable(LoxCallable::UserDefined(method))
            })
            .ok_or(RloxError::UndefinedProperty(name.to_owned()))
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
        LoxClassWalker::new(self.superclass.as_deref())
    }
}

/// Searches through `walker's` inheritance tree for `name`
///
/// In the worst case this routine is O(m*n) where m in the number methods on
/// `candidate` and `n` is inheritance depth.
fn find_method<'a, W>(mut walker: W, name: &str) -> Option<&'a LoxFunction>
where
    W: Walk<'a, Item = &'a LoxClass>,
{
    while let Some(candidate) = walker.walk() {
        if let Some(method) = candidate.methods.iter().find(|e| e.name.lexeme == name) {
            return Some(method);
        }
    }

    None
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

impl Expr {
    pub fn as_variable_unchecked(&self) -> &Token {
        match self {
            Self::Variable(t) => t,
            _ => panic!(),
        }
    }
}

// TODO: making this clone is :((
#[derive(Eq, Hash, Debug, PartialEq, Clone)]
pub struct LoxFunction {
    name: Token,
    parameters: Vec<Token>,
    body: Vec<Stmt>,
    this: Option<LoxInstance>,
    superclass: Option<LoxClass>,
    initializer: bool,
    environment: Option<usize>,
}

#[derive(Eq, Hash, Debug, PartialEq, Clone)]
pub enum Stmt {
    Block(Vec<Stmt>),
    // TODO maybe this should be Vec of LoxCallable?
    Class(Token, Option<Expr>, Vec<Stmt>),
    Expression(Expr),
    Function(LoxFunction),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    Print(Expr),
    Return(Token, Option<Expr>),
    Var(Token, Option<Expr>),
    While(Expr, Box<Stmt>),
}

impl Stmt {
    fn into_function_unchecked(self) -> LoxFunction {
        match self {
            Self::Function(f) => f,
            _ => panic!(),
        }
    }

    fn as_function_unchecked(&self) -> &LoxFunction {
        match self {
            Self::Function(f) => f,
            _ => panic!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    mod lox_instance {
        use super::*;

        #[test]
        fn it_can_lookup_methods() {
            let method = LoxFunction {
                name: Token::new(TokenType::Identifier, "bar".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                superclass: None,
                environment: None,
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
            let mut method = LoxFunction {
                name: Token::new(TokenType::Identifier, "f".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                superclass: None,
                environment: None,
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
            let mut method = LoxFunction {
                name: Token::new(TokenType::Identifier, "f".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                superclass: None,
                environment: None,
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
            let mut method = LoxFunction {
                name: Token::new(TokenType::Identifier, "f".to_owned(), 1),
                parameters: Vec::new(),
                body: Vec::new(),
                this: None,
                initializer: false,
                superclass: None,
                environment: None,
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

        fn make_method(name: &str, superclass: Option<LoxClass>) -> LoxFunction {
            LoxFunction {
                name: Token::new(TokenType::Identifier, name.to_owned(), 1),
                parameters: Vec::default(),
                body: Vec::default(),
                this: None,
                initializer: false,
                superclass,
                environment: Some(0),
            }
        }

        #[test]
        fn it_can_walk_an_inheritance_tree() {
            let grandparent = LoxClass::new("grandparent".to_owned(), None);
            let parent = LoxClass::new("parent".to_owned(), Some(Box::new(grandparent.clone())));
            let child = LoxClass::new("child".to_owned(), Some(Box::new(parent.clone())));

            let mut walker = LoxClassWalker::new(child.superclass.as_deref());

            assert_eq!(Some(&parent), walker.walk());
            assert_eq!(Some(&grandparent), walker.walk());
            assert_eq!(None, walker.walk());
        }

        #[test]
        fn it_can_find_methods() {
            let mut grandparent = LoxClass::new("grandparent".to_owned(), None);
            let foo = make_method("foo", None);
            let bar = make_method("bar", None);
            let baz = make_method("baz", None);
            let qux = make_method("qux", None);

            grandparent.add_method(foo.clone());
            grandparent.add_method(bar.clone());
            grandparent.add_method(baz.clone());
            grandparent.add_method(qux.clone());

            let parent = LoxClass::new("parent".to_owned(), Some(Box::new(grandparent.clone())));
            let child = LoxClass::new("child".to_owned(), Some(Box::new(parent.clone())));

            assert_eq!(Some(&foo), find_method(child.walker(), "foo"));
        }

        #[test]
        fn it_can_find_methods_intermediates() {
            let mut grandparent = LoxClass::new("grandparent".to_owned(), None);
            let foo = make_method("foo", None);
            let bar = make_method("bar", None);
            let baz = make_method("baz", None);
            let qux = make_method("qux", None);

            grandparent.add_method(foo.clone());
            grandparent.add_method(bar.clone());
            grandparent.add_method(baz.clone());
            grandparent.add_method(qux.clone());

            let mut parent =
                LoxClass::new("parent".to_owned(), Some(Box::new(grandparent.clone())));
            let a = make_method("a", Some(grandparent.clone()));
            let b = make_method("b", Some(grandparent.clone()));
            let c = make_method("c", Some(grandparent.clone()));
            let d = make_method("d", Some(grandparent.clone()));

            parent.add_method(a.clone());
            parent.add_method(b.clone());
            parent.add_method(c.clone());
            parent.add_method(d.clone());

            let child = LoxClass::new("child".to_owned(), Some(Box::new(parent.clone())));

            assert_eq!(Some(&qux), find_method(child.walker(), "qux"));
        }
    }
}
