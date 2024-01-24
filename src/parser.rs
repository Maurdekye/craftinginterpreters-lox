use std::fmt::{Debug, Display};

use thiserror::Error as ThisError;

use crate::{
    lexer::{Token, Tokens},
    util::Peekable,
    Errors, Located, LocatedAt,
};

#[derive(Clone, Debug, ThisError)]
pub enum Error {}

impl LocatedAt<Located<Token>> for Error {}

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

type TokenIter<'a> = Peekable<Peekable<Tokens<'a>>>;
type ParseResult = Result<Expression, Errors<Located<Error>>>;

pub fn parse(tokens: Tokens<'_>) -> ParseResult {
    let mut iter = Peekable::new_double(tokens);
    expression(&mut iter)
}

fn expression(tokens: &mut TokenIter) -> ParseResult {
    equality(tokens)
}

fn equality(tokens: &mut TokenIter) -> ParseResult {
    let mut expression = comparison(tokens)?;
    while let Some(Ok(Located {
        item: Token::EqualEqual | Token::BangEqual,
        ..
    })) = tokens.peek()
    {
        let operator = tokens.next().unwrap().unwrap();
        let rhs_expression = comparison(tokens)?;
        expression = Expression::Binary(operator, expression.into(), rhs_expression.into());
    }
    Ok(expression)
}

fn comparison(tokens: &mut TokenIter) -> ParseResult {
    todo!()
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
