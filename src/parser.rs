use std::{
    fmt::{Debug, Display},
    iter::once,
};

use thiserror::Error as ThisError;

use crate::{
    lexer::Token::{self, *},
    util::{Errors, Located, MaybeLocated, MaybeLocatedAt, Peekable},
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
    Grouping(Box<Expression>),
    Unary(Located<Token>, Box<Expression>),
    Binary(Located<Token>, Box<Expression>, Box<Expression>),
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Literal(Located { item: token, .. }) => write!(f, "{token}"),
            Expression::Grouping(expr) => write!(f, "(group {expr})"),
            Expression::Unary(Located { item: token, .. }, expr) => write!(f, "({token} {expr})"),
            Expression::Binary(Located { item: token, .. }, lhs, rhs) => {
                write!(f, "({token} {lhs} {rhs})")
            }
            Expression::Ternary(cond, true_expr, false_expr) => {
                write!(f, "(? {cond} {true_expr} {false_expr})")
            }
        }
    }
}

pub fn parse(
    tokens: impl Iterator<Item = Located<Token>>,
) -> Result<Expression, Errors<MaybeLocated<Error>>> {
    let mut iter = Peekable::new(tokens);
    expression(&mut iter).map_err(|e| once(e).collect())
}

type ExpressionParseResult = Result<Expression, MaybeLocated<Error>>;

fn expression(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> ExpressionParseResult {
    ternary(tokens)
}

fn ternary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    if let Some(operator) =
        tokens.next_if(|token: &Located<Token>| matches!(token.item, QuestionMark | Colon))
    {
        return Err(Error::UnexpectedTernaryOperator(operator.item.clone()).located_at(&operator));
    }
    let mut expression = binary(tokens)?;
    while let Some(operator) = tokens.next_if(|token| matches!(token.item, QuestionMark)) {
        let true_expr = binary(tokens).map_err(|err| {
            Error::TernaryExpressionTrueBranchParse(err.into()).located_at(&operator)
        })?;
        let colon_token = tokens.next();
        let Some(Located { item: Colon, .. }) = colon_token else {
            return Err(Error::MissingTernaryColon.located_if(colon_token.as_ref()));
        };
        let false_expr = binary(tokens).map_err(|err| {
            Error::TernaryExpressionFalseBranchParse(err.into()).located_if(colon_token.as_ref())
        })?;
        expression = Expression::Ternary(expression.into(), true_expr.into(), false_expr.into());
    }
    Ok(expression)
}

fn binary_parse<F, I>(
    tokens: &mut Peekable<I>,
    operator_pred: impl Fn(&Token) -> bool,
    mut sub_parser: F,
) -> ExpressionParseResult
where
    I: Iterator<Item = Located<Token>>,
    F: FnMut(&mut Peekable<I>) -> ExpressionParseResult,
{
    if let Some(operator) =
        tokens.next_if(|token| operator_pred(&token.item) && !matches!(token.item, Minus))
    {
        return Err(Error::UnexpectedBinaryOperator(operator.item.clone()).located_at(&operator));
    }
    let mut expression = sub_parser(tokens)?;
    while let Some(operator) = tokens.next_if(|token| operator_pred(&token.item)) {
        let rhs_expression = sub_parser(tokens)
            .map_err(|err| Error::BinaryExpressionParse(err.into()).located_at(&operator))?;
        expression = Expression::Binary(operator, expression.into(), rhs_expression.into());
    }
    Ok(expression)
}

fn binary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    binary_parse(
        tokens,
        |t| matches!(t, EqualEqual | BangEqual),
        |tokens| {
            binary_parse(
                tokens,
                |t| matches!(t, Greater | GreaterEqual | Less | LessEqual),
                |tokens| {
                    binary_parse(
                        tokens,
                        |t| matches!(t, Minus | Plus),
                        |tokens| binary_parse(tokens, |t| matches!(t, Slash | Star), unary),
                    )
                },
            )
        },
    )
}

fn unary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    if let Some(operator) = tokens.next_if(|token| matches!(token.item, Bang | Minus)) {
        let rhs = unary(tokens)
            .map_err(|err| Error::UnaryExpressionParse(err.into()).located_at(&operator))?;
        Ok(Expression::Unary(operator, rhs.into()))
    } else {
        primary(tokens)
    }
}

fn primary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    let Some(next_token) = tokens.next() else {
        return Err(Error::UnexpectedEndOfTokenStream.unlocated());
    };

    match next_token.item {
        False | True | Nil | Number(_) | String(_) => Ok(Expression::Literal(next_token)),
        LeftParen => {
            let sub_expression = expression(tokens)?;
            let close_token = tokens.next();
            let Some(Located {
                item: RightParen, ..
            }) = close_token
            else {
                return Err(
                    Error::UnclosedOpeningParen(next_token.line, next_token.character)
                        .located_if(close_token.as_ref()),
                );
            };
            Ok(Expression::Grouping(sub_expression.into()))
        }
        _ => Err(Error::UnexpectedToken(next_token.item.clone()).located_at(&next_token)),
    }
}
