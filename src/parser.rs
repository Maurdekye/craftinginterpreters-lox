use std::fmt::{Debug, Display};

use crate::lexer::Token;

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
    Equality(Box<Equality>, Token, Comparison),
    Comparison(Comparison),
}

impl Display for Equality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Equality::Equality(equality, operation, comparison) => {
                write!(f, "({operation} {equality} {comparison})")
            }
            Equality::Comparison(comparison) => write!(f, "{comparison}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Comparison {
    Comparison(Box<Comparison>, Token, Term),
    Term(Term),
}

impl Display for Comparison {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Comparison::Comparison(comparison, operation, term) => {
                write!(f, "({operation} {comparison} {term})")
            }
            Comparison::Term(term) => write!(f, "{term}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Term {
    Term(Box<Term>, Token, Factor),
    Factor(Factor),
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Term(term, operation, factor) => write!(f, "({operation} {term} {factor})"),
            Term::Factor(factor) => write!(f, "{factor}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Factor {
    Factor(Box<Factor>, Token, Unary),
    Unary(Unary),
}

impl Display for Factor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Factor::Factor(factor, operation, unary) => write!(f, "({operation} {factor} {unary})"),
            Factor::Unary(unary) => write!(f, "{unary}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Unary {
    Unary(Token, Box<Unary>),
    Primary(Primary),
}

impl Display for Unary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unary::Unary(operation, unary) => write!(f, "({operation} {unary})"),
            Unary::Primary(primary) => write!(f, "{primary}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Primary {
    Grouping(Box<Expression>),
    Literal(Token),
}

impl Display for Primary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Primary::Grouping(expr) => write!(f, "(group {expr})"),
            Primary::Literal(literal) => write!(f, "{literal}"),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::{Comparison, Equality, Expression, Factor, Primary, Term, Unary};
    use crate::lexer::Token::*;

    #[test]
    fn test() {
        let expr = Expression::Equality(Equality::Comparison(Comparison::Term(Term::Factor(
            Factor::Factor(
                Factor::Unary(Unary::Unary(
                    Minus,
                    Unary::Primary(Primary::Literal(Number(123f64))).into(),
                ))
                .into(),
                Star,
                Unary::Primary(Primary::Grouping(
                    Expression::Equality(Equality::Comparison(Comparison::Term(Term::Factor(
                        Factor::Unary(Unary::Primary(Primary::Literal(Number(45.67)))),
                    ))))
                    .into(),
                )),
            ),
        ))));

        assert_eq!(format!("{expr}"), "(* (- 123) (group 45.67))");
    }
}
