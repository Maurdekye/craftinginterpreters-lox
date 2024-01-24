use std::{
    fmt::{Debug, Display},
    iter::once,
};

use thiserror::Error as ThisError;

use crate::{
    lexer::{
        Token::{self, *},
        Tokens,
    },
    util::Peekable,
    Errors, Located, LocatedAt,
};

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Error parsing binary expression:\n{0}")]
    BinaryExpressionParse(Box<MaybeLocated<Error>>),
    #[error("Error parsing unary expression:\n{0}")]
    UnaryExpressionParse(Box<MaybeLocated<Error>>),
    #[error("Unexpected end of token stream")]
    UnexpectedEndOfTokenStream,
    #[error("Missing ')' after expression end")]
    UnclosedOpeningParen,
    #[error("Unexpected token: {0}")]
    UnexpectedToken(Token),
}

#[derive(Clone, Debug, ThisError)]
pub enum MaybeLocated<T> {
    Located(Located<T>),
    Unlocated(T),
}

impl<T: Display> Display for MaybeLocated<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeLocated::Located(located) => write!(f, "{located}"),
            MaybeLocated::Unlocated(unlocated) => write!(f, "{unlocated}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(Located<Token>),
    Grouping(Box<Expression>),
    Unary(Located<Token>, Box<Expression>),
    Binary(Located<Token>, Box<Expression>, Box<Expression>),
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

fn binary_parse<F, I>(
    tokens: &mut Peekable<I>,
    operator_pred: impl Fn(&Token) -> bool,
    mut sub_parser: F,
) -> ExpressionParseResult
where
    I: Iterator<Item = Located<Token>>,
    F: FnMut(&mut Peekable<I>) -> ExpressionParseResult,
{
    let mut expression = sub_parser(tokens)?;
    while let Some(operator) = tokens.next_if(|token| operator_pred(&token.item)) {
        let rhs_expression = sub_parser(tokens).map_err(|err| {
            MaybeLocated::Located(Error::BinaryExpressionParse(err.into()).at(&operator))
        })?;
        expression = Expression::Binary(operator, expression.into(), rhs_expression.into());
    }
    Ok(expression)
}

fn expression(
    tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>,
) -> ExpressionParseResult {
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
        let rhs = unary(tokens).map_err(|err| {
            MaybeLocated::Located(Error::UnaryExpressionParse(err.into()).at(&operator))
        })?;
        Ok(Expression::Unary(operator, rhs.into()))
    } else {
        primary(tokens)
    }
}

fn primary(tokens: &mut Peekable<impl Iterator<Item = Located<Token>>>) -> ExpressionParseResult {
    let Some(next_token) = tokens.next() else {
        return Err(MaybeLocated::Unlocated(Error::UnexpectedEndOfTokenStream));
    };

    match next_token.item {
        False | True | Nil | Number(_) | String(_) => Ok(Expression::Literal(next_token)),
        LeftParen => {
            let sub_expression = expression(tokens)?;
            let next_token = tokens.next();
            let Some(Located {
                item: RightParen, ..
            }) = next_token
            else {
                return Err(next_token.map_or(
                    MaybeLocated::Unlocated(Error::UnclosedOpeningParen),
                    |next_token| MaybeLocated::Located(Error::UnclosedOpeningParen.at(&next_token)),
                ));
            };
            Ok(Expression::Grouping(sub_expression.into()))
        }
        _ => Err(MaybeLocated::Located(
            Error::UnexpectedToken(next_token.item.clone()).at(&next_token),
        )),
    }
}

#[cfg(test)]
mod tests {

    use super::Expression::*;
    use crate::{lexer::Token::*, Located};

    #[test]
    fn test() {
        let expr = Binary(
            Located {
                line: 1,
                character: 1,
                item: Star,
            },
            Unary(
                Located {
                    line: 1,
                    character: 1,
                    item: Minus,
                },
                Literal(Located {
                    line: 1,
                    character: 1,
                    item: Number(123f64),
                })
                .into(),
            )
            .into(),
            Grouping(
                Literal(Located {
                    line: 1,
                    character: 1,
                    item: Number(45.67),
                })
                .into(),
            )
            .into(),
        );

        assert_eq!(format!("{expr}"), "(* (- 123) (group 45.67))");
    }
}
