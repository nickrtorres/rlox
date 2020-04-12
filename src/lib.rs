#![warn(clippy::pedantic)]
#![feature(str_strip)]
use std::clone::Clone;
use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;
use std::string::ToString;

#[derive(Debug, Clone, PartialEq)]
enum TokenType {
    /// Single-character tokens
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

impl TokenType {
    /// TODO rename this
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
struct Token {
    token_type: TokenType,
    lexeme: String,
    line: usize,
}

impl Token {
    pub fn new(token_type: TokenType, lexeme: String, line: usize) -> Self {
        Token {
            token_type,
            lexeme,
            line,
        }
    }
}

impl ToString for Token {
    fn to_string(&self) -> String {
        format!("{} {} ", stringify!(self.token_type), self.lexeme,)
    }
}

struct Scanner<'a> {
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
    fn new(source: &'a str) -> Self {
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
}
