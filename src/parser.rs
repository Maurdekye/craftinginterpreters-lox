use std::{fmt::{Debug, Display}, path::Iter};

use crate::{lexer::{Token, TokenLocation, Tokens}, util::Peekable};

#[derive(Clone, Debug)]
pub enum Expression {
    Equality(Equality),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Equality(equality) => write!(f, "{equality}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Equality {
    Equality(Box<Equality>, TokenLocation, Comparison),
    Comparison(Comparison),
}

impl Display for Equality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Equality::Equality(equality, TokenLocation { token, .. }, comparison) => {
                write!(f, "({token} {equality} {comparison})")
            }
            Equality::Comparison(comparison) => write!(f, "{comparison}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Comparison {
    Comparison(Box<Comparison>, TokenLocation, Term),
    Term(Term),
}

impl Display for Comparison {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Comparison::Comparison(comparison, TokenLocation { token, .. }, term) => {
                write!(f, "({token} {comparison} {term})")
            }
            Comparison::Term(term) => write!(f, "{term}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Term {
    Term(Box<Term>, TokenLocation, Factor),
    Factor(Factor),
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Term(term, TokenLocation { token, .. }, factor) => {
                write!(f, "({token} {term} {factor})")
            }
            Term::Factor(factor) => write!(f, "{factor}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Factor {
    Factor(Box<Factor>, TokenLocation, Unary),
    Unary(Unary),
}

impl Display for Factor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Factor::Factor(factor, TokenLocation { token, .. }, unary) => {
                write!(f, "({token} {factor} {unary})")
            }
            Factor::Unary(unary) => write!(f, "{unary}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Unary {
    Unary(TokenLocation, Box<Unary>),
    Primary(Primary),
}

impl Display for Unary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unary::Unary(TokenLocation { token, .. }, unary) => write!(f, "({token} {unary})"),
            Unary::Primary(primary) => write!(f, "{primary}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Primary {
    Grouping(Box<Expression>),
    Literal(TokenLocation),
}

impl Display for Primary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Primary::Grouping(expr) => write!(f, "(group {expr})"),
            Primary::Literal(TokenLocation { token, .. }) => write!(f, "{token}"),
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

    use super::{Comparison, Equality, Expression, Factor, Primary, Term, Unary};
    use crate::lexer::{Token::*, TokenLocation};

    #[test]
    fn test() {
        let expr = Expression::Equality(Equality::Comparison(Comparison::Term(Term::Factor(
            Factor::Factor(
                Factor::Unary(Unary::Unary(
                    TokenLocation {
                        line: 1,
                        character: 1,
                        token: Minus,
                    },
                    Unary::Primary(Primary::Literal(TokenLocation {
                        line: 1,
                        character: 1,
                        token: Number(123f64),
                    }))
                    .into(),
                ))
                .into(),
                TokenLocation {
                    line: 1,
                    character: 1,
                    token: Star,
                },
                Unary::Primary(Primary::Grouping(
                    Expression::Equality(Equality::Comparison(Comparison::Term(Term::Factor(
                        Factor::Unary(Unary::Primary(Primary::Literal(TokenLocation {
                            line: 1,
                            character: 1,
                            token: Number(45.67),
                        }))),
                    ))))
                    .into(),
                )),
            ),
        ))));

        assert_eq!(format!("{expr}"), "(* (- 123) (group 45.67))");
    }
}
