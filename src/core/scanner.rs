use std::iter::Peekable;

use owned_chars::OwnedChars;

use super::{Result, RloxError, Token, TokenType};

pub struct Scanner {
    // Scratch pad for Tokens
    scratch: String,
    chars: Peekable<OwnedChars>,
    // Consider making tokens, start and current Cell's to avoid
    // having to hold a mut Scanner
    tokens: Vec<Token>,
    line: usize,
}

impl Scanner {
    /// Creates a new `Scanner` whose referent is `source`.
    ///
    /// Note, a `Scanner` is only valid for the lifetime of source since a
    /// scanner is really just an encapsulated iterator over a given source
    /// `String`. Rather than having the `Scanner`s own Strings, just store a
    /// shared reference to the source input as a `Peekable<Chars>` iterator
    #[must_use]
    pub fn new(source: String) -> Self {
        Scanner {
            // cautiously optimistic allocation
            scratch: String::with_capacity(1024),
            chars: OwnedChars::from_string(source).peekable(),
            tokens: Vec::new(),
            line: 1,
        }
    }

    /// Returns the list of Tokens owned by self
    pub fn scan_tokens<'s>(mut self) -> Result<Vec<Token>> {
        while let Some(c) = self.advance() {
            self.scan_token(c)?;
            self.scratch.clear();
        }

        self.tokens
            .push(Token::new(TokenType::Eof, String::new(), self.line));

        Ok(self.tokens)
    }

    fn scan_token(&mut self, c: char) -> Result<()> {
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

                    self.line += 1;
                } else {
                    self.add_token(TokenType::Slash);
                }
            }
            '\n' => self.line += 1,
            '"' => self.string()?,
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

        Ok(())
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

    fn string(&mut self) -> Result<()> {
        while let Some(s) = self.advance() {
            if s == '"' {
                break;
            }
        }

        // It should be impossible to get here if the string does not start with a \"
        assert!(self.scratch.starts_with("\""));
        let value = self
            .scratch
            .strip_prefix("\"")
            .expect("String does not start with \"!")
            .to_owned();

        self.add_token(TokenType::String(String::from(
            value
                .strip_suffix("\"")
                .ok_or(RloxError::UnterminatedString(self.line))?,
        )));

        Ok(())
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
    fn it_can_scan_numerous_tokens_expression() {
        let scanner = Scanner::new("var breakfast;".to_owned());
        let actual = scanner.scan_tokens().unwrap();
        // 'var' , 'breakfast' , ';' , 'EOF'
        assert_eq!(4, actual.len());

        let expected = vec![
            Token::new(TokenType::Var, String::from("var"), 1),
            Token::new(TokenType::Identifier, String::from("breakfast"), 1),
            Token::new(TokenType::Semicolon, String::from(";"), 1),
            Token::new(TokenType::Eof, String::from(""), 1),
        ];

        for (actual, expected) in actual.iter().zip(expected.iter()) {
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn it_can_scan_numerous_tokens_assignment() {
        let scanner = Scanner::new("var breakfast = \"bagels\";".to_owned());
        let actual = scanner.scan_tokens().unwrap();
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

        for (actual, expected) in actual.iter().zip(expected.iter()) {
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn it_can_scan_numerous_tokens_conditional_with_newlines() {
        let scanner = Scanner::new(
            "if (condition) {\n  print \"yes\";\n} else {\n  print \"no\";\n}\n".to_owned(),
        );
        let actual = scanner.scan_tokens().unwrap();
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

        for (actual, expected) in actual.iter().zip(expected.iter()) {
            assert_eq!(actual, expected);
        }
    }
}
