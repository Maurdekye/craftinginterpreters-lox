use std::fmt::{Debug, Display};

use thiserror::Error as ThisError;

use crate::{
    lexer::Token,
    util::{
        AppendMaybeLocatedError, Errors, Locateable, Located, LocatedAt, Location, MaybeLocated,
        MaybeLocatedAt, Peekable,
    },
};

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Error parsing true branch of ternary expression:\n{0}")]
    TernaryExpressionTrueBranchParse(Box<MaybeLocated<Error>>),
    #[error("Error parsing false branch of ternary expression:\n{0}")]
    TernaryExpressionFalseBranchParse(Box<MaybeLocated<Error>>),
    #[error("Error parsing right hand side of binary expression:\n{0}")]
    BinaryExpressionParse(Box<MaybeLocated<Error>>),
    #[error("Error parsing unary expression:\n{0}")]
    UnaryExpressionParse(Box<MaybeLocated<Error>>),

    #[error("Error parsing print statement:\n{0}")]
    PrintStatementParse(Box<MaybeLocated<Error>>),
    #[error("Error parsing expression statement:\n{0}")]
    ExpressionStatementParse(Box<MaybeLocated<Error>>),
    #[error("Error parsing variable declaration:\n{0}")]
    VarStatementParse(Box<MaybeLocated<Error>>),

    #[error("Missing identifier in variable declaration")]
    MissingVarIdentifier,
    #[error("Missing semicolon at end of statement")]
    MissingSemicolon,
    #[error("Unexpected end of token stream")]
    UnexpectedEndOfTokenStream,
    #[error("Unclosed opening paren at [{0}:{1}]")]
    UnclosedOpeningParen(usize, usize),
    #[error("Unexpected token: '{0}'")]
    UnexpectedToken(Token),
    #[error("Unexpected binary operator without expression: '{0}'")]
    UnexpectedBinaryOperator(Token),
    #[error("Unexpected ternary operator without expression: '{0}'")]
    UnexpectedTernaryOperator(Token),
    #[error("Missing ':' in ternary expression")]
    MissingTernaryColon,
}

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(Located<Token>),
    Variable(String),
    Grouping(Located<Box<Expression>>),
    Unary(Located<Token>, Located<Box<Expression>>),
    Binary(
        Located<Token>,
        Located<Box<Expression>>,
        Located<Box<Expression>>,
    ),
    Ternary(
        Located<Box<Expression>>,
        Located<Box<Expression>>,
        Located<Box<Expression>>,
    ),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Literal(Located { item: token, .. }) => write!(f, "{token}"),
            Expression::Variable(name) => write!(f, "(variable {name})"),
            Expression::Grouping(Located { item: expr, .. }) => write!(f, "(group {expr})"),
            Expression::Unary(Located { item: token, .. }, expr) => write!(f, "({token} {expr})"),
            Expression::Binary(Located { item: token, .. }, lhs, rhs) => {
                write!(f, "({token} {lhs} {rhs})")
            }
            Expression::Ternary(
                Located { item: cond, .. },
                Located {
                    item: true_expr, ..
                },
                Located {
                    item: false_expr, ..
                },
            ) => {
                write!(f, "(? {cond} {true_expr} {false_expr})")
            }
        }
    }
}

impl From<Located<Expression>> for Located<Box<Expression>> {
    fn from(value: Located<Expression>) -> Self {
        let location = value.location();
        Box::new(value.item).at(&location)
    }
}

#[derive(Clone, Debug)]
pub enum Statement {
    Print(Located<Expression>),
    Expression(Located<Expression>),
    Var(String, Option<Located<Expression>>),
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Print(expression) => writeln!(f, "(print {})", expression.item),
            Statement::Expression(expression) => writeln!(f, "{}", expression.item),
            Statement::Var(name, None) => {
                writeln!(f, "(var {})", name)
            }
            Statement::Var(name, Some(expression)) => {
                writeln!(f, "(var {} {})", name, expression.item)
            }
        }
    }
}

fn synchronize(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) {
    while let Some(_) = tokens.next_if(|token| {
        !matches!(
            token.item,
            Token::Semicolon
                | Token::Class
                | Token::Fun
                | Token::Var
                | Token::For
                | Token::If
                | Token::While
                | Token::Print
                | Token::Return
        )
    }) {}
    tokens.next_if(|token| matches!(token.item, Token::Semicolon));
}

fn consume(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
    pred: impl FnOnce(&Token) -> bool,
    error_factory: impl FnOnce() -> Error,
) -> Result<Location, MaybeLocated<Error>> {
    match tokens.peek() {
        Some(located_token @ Located { item: token, .. }) => {
            let location = located_token.location();
            if pred(&token) {
                tokens.next();
                Ok(location)
            } else {
                Err(error_factory().located_at(&location))
            }
        }
        None => Err(error_factory().unlocated()),
    }
}

fn consume_semicolon(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> Result<Location, MaybeLocated<Error>> {
    consume(
        tokens,
        |t| matches!(t, Token::Semicolon),
        || Error::MissingSemicolon,
    )
}

pub fn parse(
    tokens: impl Iterator<Item = Located<Token>>,
) -> Result<Vec<Located<Statement>>, Errors<MaybeLocated<Error>>> {
    let mut tokens = Peekable::new(tokens);
    let mut statements = Vec::new();
    let mut errors = Errors::new();

    loop {
        match tokens.peek() {
            Some(Located {
                item: Token::Eof, ..
            }) => break,
            Some(_) => match declaration(&mut tokens) {
                Ok(statement) => statements.push(statement),
                Err(err) => {
                    errors.push(err);
                    synchronize(&mut tokens);
                }
            },
            None => {
                errors.push(Error::UnexpectedEndOfTokenStream.unlocated());
                break;
            }
        }
    }

    errors.empty_ok(statements)
}

fn declaration(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> Result<Located<Statement>, MaybeLocated<Error>> {
    match tokens.peek() {
        Some(
            var_token @ Located {
                item: Token::Var, ..
            },
        ) => {
            let location = var_token.location();
            (|| {
                tokens.next();
                let Some(Located {
                    item: Token::Identifier(name),
                    ..
                }) = tokens.next()
                else {
                    return Err(Error::MissingVarIdentifier.located_at(&location));
                };
                match tokens.next() {
                    Some(Located {
                        item: Token::Semicolon,
                        ..
                    }) => Ok(Statement::Var(name, None).at(&location)),
                    Some(Located {
                        item: Token::Equal, ..
                    }) => {
                        let var_expr = expression(tokens)?;
                        consume_semicolon(tokens)?;
                        Ok(Statement::Var(name, Some(var_expr)).at(&location))
                    }
                    Some(unexpected_token) => {
                        let token_location = unexpected_token.location();
                        Err(Error::UnexpectedToken(unexpected_token.item)
                            .located_at(&token_location))
                    }
                    None => Err(Error::UnexpectedEndOfTokenStream.unlocated()),
                }
            })()
            .with_err_located_at(Error::VarStatementParse, &location)
        }
        _ => statement(tokens),
    }
}

fn statement(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> Result<Located<Statement>, MaybeLocated<Error>> {
    match tokens.peek() {
        Some(
            print_token @ Located {
                item: Token::Print, ..
            },
        ) => {
            let location = print_token.location();
            (|| {
                tokens.next();
                let expr: Located<Expression> = expression(tokens)?;
                consume_semicolon(tokens)?;
                Ok::<_, MaybeLocated<Error>>(Statement::Print(expr).at(&location))
            })()
            .with_err_located_at(Error::PrintStatementParse, &location)
        }
        Some(expression_token) => {
            let location = expression_token.location();
            (|| {
                let expr = expression(tokens)?;
                consume_semicolon(tokens)?;
                Ok::<_, MaybeLocated<Error>>(Statement::Expression(expr).at(&location))
            })()
            .with_err_located_at(Error::ExpressionStatementParse, &location)
        }
        None => Err(Error::UnexpectedEndOfTokenStream.unlocated()),
    }
}

type ExpressionParseResult = Result<Located<Expression>, MaybeLocated<Error>>;

fn expression(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> ExpressionParseResult {
    ternary(tokens)
}

fn ternary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    if let Some(operator) = tokens
        .next_if(|token: &Located<Token>| matches!(token.item, Token::QuestionMark | Token::Colon))
    {
        return Err(Error::UnexpectedTernaryOperator(operator.item.clone()).located_at(&operator));
    }
    let mut expression = binary(tokens)?;
    while let Some(operator) = tokens.next_if(|token| matches!(token.item, Token::QuestionMark)) {
        let true_expr = binary(tokens)
            .with_err_located_at(Error::TernaryExpressionTrueBranchParse, &operator)?;
        let colon_token_location = consume(
            tokens,
            |t| matches!(t, Token::Colon),
            || Error::MissingTernaryColon,
        )?;
        let false_expr = binary(tokens).with_err_located_at(
            Error::TernaryExpressionFalseBranchParse,
            &colon_token_location,
        )?;
        let location = expression.location();
        expression = Expression::Ternary(expression.into(), true_expr.into(), false_expr.into())
            .at(&location);
    }
    Ok(expression)
}

fn binary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    fn binary_parse<F, I>(
        tokens: &mut Peekable<I>,
        operator_pred: impl Fn(&Token) -> bool,
        mut sub_parser: F,
    ) -> ExpressionParseResult
    where
        I: Iterator<Item = Located<Token>>,
        F: FnMut(&mut Peekable<I>) -> ExpressionParseResult,
    {
        if let Some(operator) = tokens
            .next_if(|token| operator_pred(&token.item) && !matches!(token.item, Token::Minus))
        {
            return Err(
                Error::UnexpectedBinaryOperator(operator.item.clone()).located_at(&operator)
            );
        }
        let mut expression = sub_parser(tokens)?;
        while let Some(operator) = tokens.next_if(|token| operator_pred(&token.item)) {
            let rhs_expression =
                sub_parser(tokens).with_err_located_at(Error::BinaryExpressionParse, &operator)?;
            let location = expression.location();
            expression = Expression::Binary(operator, expression.into(), rhs_expression.into())
                .at(&location);
        }
        Ok(expression)
    }
    binary_parse(
        tokens,
        |t| matches!(t, Token::And | Token::Or),
        |tokens| {
            binary_parse(
                tokens,
                |t| matches!(t, Token::EqualEqual | Token::BangEqual),
                |tokens| {
                    binary_parse(
                        tokens,
                        |t| {
                            matches!(
                                t,
                                Token::Greater
                                    | Token::GreaterEqual
                                    | Token::Less
                                    | Token::LessEqual
                            )
                        },
                        |tokens| {
                            binary_parse(
                                tokens,
                                |t| matches!(t, Token::Minus | Token::Plus),
                                |tokens| {
                                    binary_parse(
                                        tokens,
                                        |t| matches!(t, Token::Slash | Token::Star),
                                        unary,
                                    )
                                },
                            )
                        },
                    )
                },
            )
        },
    )
}

fn unary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    if let Some(operator) = tokens.next_if(|token| matches!(token.item, Token::Bang | Token::Minus))
    {
        let location = operator.location();
        let rhs = unary(tokens).with_err_located_at(Error::UnaryExpressionParse, &location)?;
        Ok(Expression::Unary(operator, rhs.into()).at(&location))
    } else {
        primary(tokens)
    }
}

fn primary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    let Some(next_token) = tokens.next() else {
        return Err(Error::UnexpectedEndOfTokenStream.unlocated());
    };
    let location = next_token.location();

    match next_token.item {
        Token::False | Token::True | Token::Nil | Token::Number(_) | Token::String(_) => {
            Ok(Expression::Literal(next_token).at(&location))
        }
        Token::Identifier(name) => Ok(Expression::Variable(name).at(&location)),
        Token::LeftParen => {
            let sub_expression = expression(tokens)?;
            let close_token = tokens.next();
            let Some(Located {
                item: Token::RightParen,
                ..
            }) = close_token
            else {
                return Err(
                    Error::UnclosedOpeningParen(next_token.line, next_token.character)
                        .located_if(close_token.as_ref()),
                );
            };
            Ok(Expression::Grouping(sub_expression.into()).at(&location))
        }
        _ => Err(Error::UnexpectedToken(next_token.item.clone()).located_at(&next_token)),
    }
}
