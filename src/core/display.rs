use std::fmt;
use std::result;

use super::{
    FunctionStmt, LoxCallable, LoxClass, LoxInstance, Object, RloxError, Token, TokenType,
    MAX_PARAMS,
};

impl fmt::Display for FunctionStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "<fn {}>", self.name.lexeme)
    }
}

impl fmt::Display for LoxCallable {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Self::Clock => write!(f, "<native fn>"),
            Self::ClassDefinition(n) => write!(f, "{}", n),
            Self::ClassInstance(n) => write!(f, "{}", n),
            Self::UserDefined(n) => write!(f, "{}", n),
        }
    }
}

impl fmt::Display for LoxClass {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{}", self.name)
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
            Self::Bool(b) => write!(f, "{}", b),
            Self::Nil => write!(f, "nil"),
            Self::Number(n) => write!(f, "{}", n),
            Self::String(s) => write!(f, "{}", s),
            Self::Time(t) => write!(f, "{}", t),
            Self::Callable(c) => write!(f, "{}", c),
        }
    }
}

impl fmt::Display for RloxError {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Self::ArgumentMismatch(expected, actual) => write!(
                f,
                "runtime error: Expected {} arguments but got {}.",
                expected, actual
            ),
            Self::ExpectedExpression(t) => write!(f, "Error at '{}': Expect expression.", t.lexeme),
            Self::ExpectedVarName(t) => write!(f, "Error at '{}': Expect variable name.", t.lexeme),
            Self::FloatParseError(line, e) => write!(f, "[line {}] {}", line, e),
            Self::InheritFromSelf(s) => {
                write!(f, "Error at '{}': A class cannot inherit from itself.", s)
            }
            Self::InheritNonClass => write!(f, "runtime error: Superclass must be a class."),
            Self::InvalidAssignment => write!(f, "Error at '=': Invalid assignment target."),
            Self::MismatchedOperands(op, left, right) => {
                write!(f, "error: invalid expression: {} {} {}", left, op, right)
            }
            Self::MissingSemicolon(line) => write!(f, "error: {}: missing semicolon", line),
            Self::NotCallable => write!(f, "runtime error: Can only call functions and classes."),
            Self::PropertyAccessOnNonInstance => {
                write!(f, "runtime error: Only instances have properties.")
            }
            Self::ReturnValueFromConstructor => write!(
                f,
                "Error at 'return': Cannot return a value from an initializer."
            ),
            Self::SuperOutsideOfClass(t) => write!(
                f,
                "Error at '{}': Cannot use '{}' outside of a class.",
                t.lexeme, t.lexeme
            ),
            Self::SuperWithoutParent(t) => write!(
                f,
                "Error at '{}': Cannot use '{}' in a class with no superclass.",
                t.lexeme, t.lexeme,
            ),
            Self::ThisOutsideOfClass => {
                write!(f, "Error at 'this': Cannot use 'this' outside of a class.")
            }
            Self::TooManyArgs(t) => write!(
                f,
                "Error at '{}': Cannot have more than {} parameters.",
                t.lexeme, MAX_PARAMS
            ),
            Self::UnclosedParenthesis(line) => write!(f, "error: {}: unclosed parenthesis", line),
            Self::UndefinedProperty(s) => write!(f, "runtime error: Undefined property '{}'.", s),
            Self::UndefinedVariable(s) => write!(f, "runtime error: Undefined variable '{}'.", s),
            Self::UnexpectedToken(expected, actual, previous) => write!(
                f,
                "[line {}] Error at '{}': Expect '{}' after '{}'.",
                actual.line, actual.lexeme, expected, previous.lexeme
            ),
            Self::UnterminatedString(l) => write!(f, "[line {}] Error: Unterminated string.", l),
            // TODO: actually handle other errors
            _ => write!(f, "{:?}", self),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        write!(f, "{} {} ", stringify!(self.token_type), self.lexeme)
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
