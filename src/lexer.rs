use std::{fmt::Display, num::ParseFloatError};

use thiserror::Error as ThisError;

use crate::util::Peekable;

#[derive(Clone, Debug)]
pub struct Error {
    line: usize,
    character: usize,
    error: ErrorKind,
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}:{}] Error: {}",
            self.line, self.character, self.error
        )
    }
}

impl std::error::Error for Error {}

#[derive(Clone, Debug, ThisError)]
pub enum ErrorKind {
    #[error("Unterminated string")]
    UnterminatedString,
    #[error("Unterminated multiline comment")]
    UnterminatedMultilineComment,
    #[error("Number parsing error")]
    NumberParseError(#[from] ParseFloatError),
    #[error("Unrecognized character: '{0}'")]
    UnrecognizedCharacer(char),
}

impl ErrorKind {
    pub fn at(self, tokenizer: &Tokens) -> Error {
        Error {
            line: tokenizer.line,
            character: tokenizer.character,
            error: self,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Token {
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

    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    Identifier(String),
    String(String),
    Number(f64),

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

impl Token {
    pub fn at(self, tokenizer: &Tokens) -> TokenLocation {
        TokenLocation {
            line: tokenizer.line,
            character: tokenizer.character,
            token: self,
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::LeftBrace => write!(f, "{{"),
            Token::RightBrace => write!(f, "}}"),
            Token::Comma => write!(f, ","),
            Token::Dot => write!(f, "."),
            Token::Minus => write!(f, "-"),
            Token::Plus => write!(f, "+"),
            Token::Semicolon => write!(f, ";"),
            Token::Slash => write!(f, "/"),
            Token::Star => write!(f, "*"),

            Token::Bang => write!(f, "!"),
            Token::BangEqual => write!(f, "!="),
            Token::Equal => write!(f, "="),
            Token::EqualEqual => write!(f, "=="),
            Token::Greater => write!(f, ">"),
            Token::GreaterEqual => write!(f, ">="),
            Token::Less => write!(f, "<"),
            Token::LessEqual => write!(f, "<="),

            Token::Identifier(id) => write!(f, "{id}"),
            Token::String(s) => write!(f, "\"{s}\""),
            Token::Number(n) => write!(f, "{n}"),

            Token::And => write!(f, "and"),
            Token::Class => write!(f, "class"),
            Token::Else => write!(f, "else"),
            Token::False => write!(f, "false"),
            Token::Fun => write!(f, "fun"),
            Token::For => write!(f, "for"),
            Token::If => write!(f, "if"),
            Token::Nil => write!(f, "nil"),
            Token::Or => write!(f, "or"),
            Token::Print => write!(f, "print"),
            Token::Return => write!(f, "return"),
            Token::Super => write!(f, "super"),
            Token::This => write!(f, "this"),
            Token::True => write!(f, "true"),
            Token::Var => write!(f, "var"),
            Token::While => write!(f, "while"),

            Token::Eof => write!(f, ""),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TokenLocation {
    pub line: usize,
    pub character: usize,
    pub token: Token,
}

#[derive(Debug)]
pub struct Tokens<'a> {
    source: Option<&'a str>,
    line: usize,
    character: usize,
}

impl<'a> Tokens<'a> {
    pub fn new(source: impl Into<&'a str>) -> Self {
        Self {
            source: Some(source.into()),
            line: 1,
            character: 1,
        }
    }

    pub fn advance(&mut self, amount: usize) {
        if let Some(source) = &mut self.source {
            *source = &source[amount..];
            self.character += amount;
        }
    }

    pub fn newline(&mut self) {
        self.advance(1);
        self.line += 1;
        self.character = 1;
    }
}

impl<'a, T: Into<&'a str>> From<T> for Tokens<'a> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl Iterator for Tokens<'_> {
    type Item = Result<TokenLocation, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        'main: loop {
            // if source has been fully consumed, end iterator
            let Some(source) = &mut self.source else {
                return None;
            };

            // start by peeking the next two characters
            let mut chars = Peekable::new_double(source.chars());

            // reached end of source, yield EOF
            if chars.peek().is_none() {
                self.source = None;
                return Some(Ok(Token::Eof.at(self)));
            }

            // skip whitespace
            if let Some(' ' | '\r' | '\t') = chars.peek() {
                self.advance(1);
                continue;
            }

            // match newline
            if let Some('\n') = chars.peek() {
                self.newline();
                continue;
            }

            // match single and dual-character tokens
            if let Some((token, advance_by)) = match (chars.peek(), chars.peek_second()) {
                (Some('('), _) => Some((Token::LeftParen, 1)),
                (Some(')'), _) => Some((Token::RightParen, 1)),
                (Some('{'), _) => Some((Token::LeftBrace, 1)),
                (Some('}'), _) => Some((Token::RightBrace, 1)),
                (Some(','), _) => Some((Token::Comma, 1)),
                (Some('.'), _) => Some((Token::Dot, 1)),
                (Some('-'), _) => Some((Token::Minus, 1)),
                (Some('+'), _) => Some((Token::Plus, 1)),
                (Some(';'), _) => Some((Token::Semicolon, 1)),
                (Some('*'), _) => Some((Token::Star, 1)),
                (Some('!'), Some('=')) => Some((Token::BangEqual, 2)),
                (Some('!'), _) => Some((Token::Bang, 1)),
                (Some('='), Some('=')) => Some((Token::EqualEqual, 2)),
                (Some('='), _) => Some((Token::Equal, 1)),
                (Some('<'), Some('=')) => Some((Token::LessEqual, 2)),
                (Some('<'), _) => Some((Token::Less, 1)),
                (Some('>'), Some('=')) => Some((Token::GreaterEqual, 2)),
                (Some('>'), _) => Some((Token::Greater, 1)),
                _ => None,
            } {
                self.advance(advance_by);
                return Some(Ok(token.at(self)));
            }

            // match comment or slash
            if let Some('/') = chars.peek() {
                match chars.peek_second() {
                    Some('/') => {
                        // comment
                        let until_line_end: usize = chars
                            .take_while(|&c| c != '\n')
                            .map(char::len_utf8)
                            .sum();
                        self.advance(until_line_end);
                        self.newline();
                        continue;
                    }
                    Some('*') => {
                        // multiline comment
                        let mut new_line = self.line;
                        let mut new_character = self.character;
                        let mut to_skip = 2;
                        // skip beginning of comment
                        chars.next();
                        chars.next();
                        while let Some(char) = chars.next() {
                            to_skip += char.len_utf8();
                            match char {
                                '\n' => {
                                    new_line += 1;
                                    new_character = 1;
                                }
                                '*' => {
                                    to_skip += 1;
                                    new_character += 1;
                                    if let Some('/') = chars.next() {
                                        self.line = new_line;
                                        self.character = new_character;
                                        *source = &source[to_skip..];
                                        continue 'main;
                                    }
                                }
                                _ => {
                                    new_character += 1;
                                }
                            }
                        }

                        // reached EOF before multiline comment terminated
                        return Some(Err(
                            ErrorKind::UnterminatedMultilineComment.at(self)
                        ));
                    }
                    _ => {
                        // slash
                        let result = Some(Ok(Token::Slash.at(self)));
                        self.advance(1);
                        return result;
                    }
                }
            }

            // match string literals
            if let Some('"') = chars.peek() {
                // skip opening quote
                chars.next();
                let mut new_line = self.line;
                let mut new_character = self.character;
                let mut to_take = 0;

                for char in chars {
                    match char {
                        '\n' => {
                            new_line += 1;
                            new_character = 1;
                        }
                        '"' => {
                            let string = String::from(&source[1..=to_take]);
                            // +2 to skip the opening and closing quotes
                            *source = &source[to_take + 2..];
                            let result = Some(Ok(Token::String(string).at(self)));
                            self.line = new_line;
                            self.character = new_character;
                            return result;
                        }
                        _ => {
                            new_character += 1;
                        }
                    }
                    to_take += char.len_utf8();
                }

                // reached EOF before string terminated
                return Some(Err(ErrorKind::UnterminatedString.at(self)));
            }

            // match number literals
            if let Some('0'..='9') = chars.peek() {
                let mut source_chars = source.chars();
                let mut to_take = 0;

                while let Some(num_char @ ('.' | '0'..='9')) = source_chars.next() {
                    if num_char == '.' {
                        if let Some('0'..='9') = source_chars.next() {
                            to_take +=
                                2 + source_chars.take_while(|c| matches!(c, '0'..='9')).count();
                        }
                        break;
                    } else {
                        to_take += 1;
                    }
                }

                let number_string = &source[..to_take];
                *source = &source[to_take..];
                let parse_result = number_string
                    .parse()
                    .map(|float| Token::Number(float).at(self))
                    .map_err(|err| ErrorKind::NumberParseError(err).at(self));
                self.character += to_take;
                return Some(parse_result);
            }

            // match identifiers & keywords
            if let Some('a'..='z' | 'A'..='Z' | '_') = chars.peek() {
                let to_take = chars
                    .take_while(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
                    .count();
                let identifier = match &source[..to_take] {
                    "and" => Token::And,
                    "class" => Token::Class,
                    "else" => Token::Else,
                    "false" => Token::False,
                    "for" => Token::For,
                    "fun" => Token::Fun,
                    "if" => Token::If,
                    "nil" => Token::Nil,
                    "or" => Token::Or,
                    "print" => Token::Print,
                    "return" => Token::Return,
                    "super" => Token::Super,
                    "this" => Token::This,
                    "true" => Token::True,
                    "var" => Token::Var,
                    "while" => Token::While,
                    ident => Token::Identifier(ident.to_string()),
                };
                let result = Some(Ok(identifier.at(self)));
                self.advance(to_take);
                return result;
            }

            // unrecognized character
            if let Some(next_char) = chars.peek() {
                *source = &source[next_char.len_utf8()..];
                let result = Some(Err(
                    ErrorKind::UnrecognizedCharacer(*next_char).at(self)
                ));
                self.character += 1;
                return result;
            }
        }
    }
}
