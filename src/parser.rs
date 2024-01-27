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
    #[error("In this ternary:\n{0}")]
    TernaryExpressionParse(Box<MaybeLocated<Error>>),
    #[error("In this binary expression:\n{0}")]
    BinaryExpressionParse(Box<MaybeLocated<Error>>),
    #[error("At this unary operator:\n{0}")]
    UnaryExpressionParse(Box<MaybeLocated<Error>>),
    #[error("In this assignment:\n{0}")]
    AssignmentExpressionParse(Box<MaybeLocated<Error>>),

    #[error("In this print statement:\n{0}")]
    PrintStatementParse(Box<MaybeLocated<Error>>),
    #[error("In this var statement:\n{0}")]
    VarStatementParse(Box<MaybeLocated<Error>>),
    #[error("In this statement:\n{0}")]
    ExpressionStatementParse(Box<MaybeLocated<Error>>),

    #[error("Where's the variable name?")]
    MissingVarIdentifier,
    #[error("You forgot a semicolon")]
    MissingSemicolon,
    #[error("That's not a variable name")]
    InvalidAssignmentTarget(Expression),
    #[error("File's ended")]
    UnexpectedEndOfTokenStream,
    #[error("You forgot a ')' for the '(' at [{0}:{1}]")]
    UnclosedOpeningParen(usize, usize),
    #[error("What's '{0}' mean?")]
    UnexpectedToken(Token),
    #[error("This '=' doesnt make sense here, it's supposed to come after a variable name in an assignment")]
    UnexpectedAssignmentOperator,
    #[error("This '{0}' doesn't make sense here, it's supposed to be used in some sort of binary expression")]
    UnexpectedBinaryOperator(Token),
    #[error("This '{0}' doesn't make sense here, it's supposed to be part of a ternary expression")]
    UnexpectedTernaryOperator(Token),
    #[error("You forgot a ':' after the true branch of your ternary expression")]
    MissingTernaryColon,
}

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(Located<Token>),
    Variable(String),
    Assignment(Located<String>, Located<Box<Expression>>),
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
            Expression::Variable(name) => write!(f, "(ref {name})"),
            Expression::Assignment(name, expr) => write!(f, "(var {name} {expr})"),
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

type StatementParseResult = Result<Located<Statement>, MaybeLocated<Error>>;

fn declaration(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> StatementParseResult {
    match tokens.peek() {
        Some(token_location @ Located { .. }) => {
            let location = token_location.location();
            match token_location.item {
                Token::Var => {
                    var(tokens, &location).with_err_located_at(Error::VarStatementParse, &location)
                }
                _ => statement(tokens),
            }
        }
        None => Err(Error::UnexpectedEndOfTokenStream.unlocated()),
    }
}

fn var(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
    location: &Location,
) -> StatementParseResult {
    tokens.next();
    let Some(Located {
        item: Token::Identifier(name),
        ..
    }) = tokens.next()
    else {
        return Err(Error::MissingVarIdentifier.located_at(location));
    };
    match tokens.next() {
        Some(Located {
            item: Token::Semicolon,
            ..
        }) => Ok(Statement::Var(name, None).at(location)),
        Some(Located {
            item: Token::Equal, ..
        }) => {
            let var_expr = expression(tokens)?;
            consume_semicolon(tokens)?;
            Ok(Statement::Var(name, Some(var_expr)).at(location))
        }
        Some(unexpected_token) => {
            let token_location = unexpected_token.location();
            Err(Error::UnexpectedToken(unexpected_token.item).located_at(&token_location))
        }
        None => Err(Error::UnexpectedEndOfTokenStream.unlocated()),
    }
}

fn statement(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> StatementParseResult {
    match tokens.peek() {
        Some(located_token @ Located { .. }) => {
            let location = located_token.location();
            match located_token.item {
                Token::Print => print(tokens, &location)
                    .with_err_located_at(Error::PrintStatementParse, &location),
                _ => expression_statement(tokens)
                    .with_err_located_at(Error::ExpressionStatementParse, &location),
            }
        }
        None => Err(Error::UnexpectedEndOfTokenStream.unlocated()),
    }
}

fn print(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
    print_location: &Location,
) -> StatementParseResult {
    tokens.next();
    let expr: Located<Expression> = expression(tokens)?;
    consume_semicolon(tokens)?;
    Ok(Statement::Print(expr).at(print_location))
}

fn expression_statement(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> StatementParseResult {
    let expr = expression(tokens)?;
    let location = expr.location();
    consume_semicolon(tokens)?;
    Ok(Statement::Expression(expr).at(&location))
}

type ExpressionParseResult = Result<Located<Expression>, MaybeLocated<Error>>;

fn expression(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> ExpressionParseResult {
    assignment(tokens)
}

fn assignment(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> ExpressionParseResult {
    fn assignment_expression(
        tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
        expression: Located<Expression>,
    ) -> ExpressionParseResult {
        let (ident_location, expression) = expression.split();
        let Expression::Variable(name) = expression else {
            return Err(Error::InvalidAssignmentTarget(expression).located_at(&ident_location));
        };
        let rhs_expression = assignment(tokens)?;
        Ok(
            Expression::Assignment(name.at(&ident_location), rhs_expression.into())
                .at(&ident_location),
        )
    }
    if let Some(operator) = tokens.next_if(|token| matches!(token.item, Token::Equal)) {
        return Err(Error::UnexpectedAssignmentOperator.located_at(&operator));
    }
    let mut expression = ternary(tokens)?;
    if let Some(_) = tokens.next_if(|token| matches!(token.item, Token::Equal)) {
        let target_location = expression.location();
        expression = assignment_expression(tokens, expression)
            .with_err_located_at(Error::AssignmentExpressionParse, &target_location)?;
    }
    Ok(expression)
}

fn ternary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    fn ternary_body(
        tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
        expression: Located<Expression>,
    ) -> ExpressionParseResult {
        let true_expr = binary(tokens)?;
        consume(
            tokens,
            |t| matches!(t, Token::Colon),
            || Error::MissingTernaryColon,
        )?;
        let false_expr = binary(tokens)?;
        let location = expression.location();
        Ok(
            Expression::Ternary(expression.into(), true_expr.into(), false_expr.into())
                .at(&location),
        )
    }
    if let Some(operator) = tokens
        .next_if(|token: &Located<Token>| matches!(token.item, Token::QuestionMark | Token::Colon))
    {
        return Err(Error::UnexpectedTernaryOperator(operator.item.clone()).located_at(&operator));
    }
    let mut expression = binary(tokens)?;
    while let Some(operator) = tokens.next_if(|token| matches!(token.item, Token::QuestionMark)) {
        expression = ternary_body(tokens, expression)
            .with_err_located_at(Error::TernaryExpressionParse, &operator)?;
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
