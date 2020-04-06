use std::string::ToString;

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
    String,
    Number,

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

struct Token {
    token_type: TokenType,
    lexeme: String,
    literal: Option<String>,
    line: usize,
}

impl Token {
    pub fn new(
        token_type: TokenType,
        lexeme: String,
        literal: Option<String>,
        line: usize,
    ) -> Self {
        Token {
            token_type,
            lexeme,
            literal,
            line,
        }
    }
}

impl ToString for Token {
    fn to_string(&self) -> String {
        format!(
            "{} {} {}",
            stringify!(self.token_type),
            self.lexeme,
            self.literal.as_ref().unwrap_or(&String::new())
        )
    }
}

struct Scanner {
    source: String,
    tokens: Vec<Token>,
    start: usize,
    current: usize,
    line: usize,
}

impl Scanner {
    fn new(source: String) -> Self {
        Scanner {
            source,
            tokens: Vec::new(),
            start: 0,
            current: 0,
            line: 1,
        }
    }

    fn scan_tokens<'a>(&'a mut self) -> &'a Vec<Token> {
        while !self.is_at_end() {
            self.start = self.current;
            self.scan_token();
        }

        self.tokens
            .push(Token::new(TokenType::Eof, String::new(), None, self.line));
        &self.tokens
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.source.len()
    }

    fn scan_token(&mut self) {
        match self.advance() {
            '(' => self.add_token(TokenType::LeftParen, None),
            ')' => self.add_token(TokenType::RightParen, None),
            '{' => self.add_token(TokenType::LeftBrace, None),
            '}' => self.add_token(TokenType::RightBrace, None),
            ',' => self.add_token(TokenType::Comma, None),
            '.' => self.add_token(TokenType::Dot, None),
            '-' => self.add_token(TokenType::Minus, None),
            '+' => self.add_token(TokenType::Plus, None),
            ';' => self.add_token(TokenType::Semicolon, None),
            '*' => self.add_token(TokenType::Star, None),
            '!' => {
                let token = if self.look_ahead_for('=') {
                    TokenType::BangEqual
                } else {
                    TokenType::Bang
                };

                self.add_token(token, None)
            }
            '=' => {
                let token = if self.look_ahead_for('=') {
                    TokenType::EqualEqual
                } else {
                    TokenType::Equal
                };

                self.add_token(token, None)
            }
            '<' => {
                let token = if self.look_ahead_for('=') {
                    TokenType::LessEqual
                } else {
                    TokenType::Less
                };

                self.add_token(token, None)
            }
            '>' => {
                let token = if self.look_ahead_for('=') {
                    TokenType::GreaterEqual
                } else {
                    TokenType::Greater
                };

                self.add_token(token, None)
            }
            '/' => {
                if self.look_ahead_for('/') {
                    while let Some(s) = self.peek() {
                        if s == '\n' {
                            break;
                        }

                        self.source.chars().next();
                    }
                } else {
                    self.add_token(TokenType::Slash, None);
                }
            }
            ' ' | '\r' | '\t' => {}
            '\n' => self.line += 1,
            '"' => self.string(),
            _ => eprintln!("{}: unexpected token", self.line),
        };
    }

    fn peek(&self) -> Option<char> {
        // ehhhh
        self.source.chars().peekable().peek().map(|s| *s)
    }

    fn string(&mut self) {
        while let Some(s) = self.peek() {
            if s == '"' {
                break;
            }
            if self.is_at_end() {
                break;
            }

            if let Some('\n') = self.peek() {
                self.line += 1;
            }

            self.advance();
        }

        self.advance();
        let value = self.source[self.start..self.current].to_string();
        self.add_token(TokenType::String, Some(value))
    }

    fn advance(&mut self) -> char {
        self.current += 1;
        self.source.chars().next().unwrap()
    }

    fn look_ahead_for(&self, expected: char) -> bool {
        if self.is_at_end() {
            return false;
        }

        if self
            .source
            .chars()
            .peekable()
            .peek()
            .map(|s| *s == expected)
            .is_some()
        {
            self.source.chars().next();
            true
        } else {
            false
        }
    }

    fn add_token(&mut self, token: TokenType, literal: Option<String>) {
        assert!(self.start < self.source.len());
        assert!(self.current < self.source.len());
        // Assumes we live in a world where a character == a byte
        let text = self.source[self.start..self.current].to_string();
        self.tokens
            .push(Token::new(token, text, literal, self.line));
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
