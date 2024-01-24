use std::{
    fmt::{Debug, Display},
    path::Iter,
};

use crate::{
    lexer::{Token, TokenLocation, Tokens},
    util::Peekable,
};

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(TokenLocation),
    Grouping(Box<Expression>),
    Unary(TokenLocation, Box<Expression>),
    Binary(TokenLocation, Box<Expression>, Box<Expression>),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Literal(TokenLocation { token, .. }) => write!(f, "{token}"),
            Expression::Grouping(expr) => write!(f, "(group {expr})"),
            Expression::Unary(TokenLocation { token, .. }, expr) => write!(f, "({token} {expr})"),
            Expression::Binary(TokenLocation { token, .. }, lhs, rhs) => {
                write!(f, "({token} {lhs} {rhs})")
            }
        }
    }
}

pub fn parse(tokens: Tokens<'_>) -> Expression {
    let mut iter = Peekable::new_double(tokens);
    expression(&mut iter)
}

fn expression(tokens: &mut Peekable<Peekable<Tokens<'_>>>) -> Expression {
    let subexpression = comparison(tokens);

    todo!()
}

fn comparison(tokens: &mut Peekable<Peekable<Tokens<'_>>>) -> Expression {
    todo!()
}

#[cfg(test)]
mod tests {

    use super::Expression::*;
    use crate::lexer::{Token::*, TokenLocation};

    #[test]
    fn test() {
        let expr = Binary(
            TokenLocation {
                line: 1,
                character: 1,
                token: Star,
            },
            Unary(
                TokenLocation {
                    line: 1,
                    character: 1,
                    token: Minus,
                },
                Literal(TokenLocation {
                    line: 1,
                    character: 1,
                    token: Number(123f64),
                })
                .into(),
            )
            .into(),
            Grouping(
                Literal(TokenLocation {
                    line: 1,
                    character: 1,
                    token: Number(45.67),
                })
                .into(),
            )
            .into(),
        );

        assert_eq!(format!("{expr}"), "(* (- 123) (group 45.67))");
    }
}
