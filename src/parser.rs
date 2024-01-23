use std::fmt::Display;

use crate::lexer::Token;

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(Token),
    Grouping(Box<Expression>),
    Equality(Token, Box<Expression>, Box<Expression>),
    Comparison(Token, Box<Expression>, Box<Expression>),
    Term(Token, Box<Expression>, Box<Expression>),
    Factor(Token, Box<Expression>, Box<Expression>),
    Unary(Token, Box<Expression>),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Literal(literal) => literal.fmt(f),
            Expression::Grouping(expr) => write!(f, "(group {expr})"),
            Expression::Unary(unary, expr) => write!(f, "({unary} {expr})"),
            Expression::Equality(operation, lhs, rhs)
            | Expression::Comparison(operation, lhs, rhs)
            | Expression::Term(operation, lhs, rhs)
            | Expression::Factor(operation, lhs, rhs) => write!(f, "({operation} {lhs} {rhs})"),
        }
    }
}

/* this may not be necessary?
impl Expression {
    pub fn accept(self, visitor: &mut impl ExpressionVisitor) {
        match self {
            Expression::Literal(literal) => visitor.visit_literal(literal),
            Expression::Grouping(expr) => visitor.visit_grouping(*expr),
            Expression::Unary(unary, expr) => visitor.visit_unary(unary, *expr),
            Expression::Binary(lhs, binary, rhs) => visitor.visit_binary(*lhs, binary, *rhs),
        }
    }
}

pub trait ExpressionVisitor {
    fn visit_literal(&mut self, literal: Literal);
    fn visit_grouping(&mut self, expr: Expression);
    fn visit_unary(&mut self, unary: Unary, expr: Expression);
    fn visit_binary(&mut self, lhs: Expression, binary: Binary, rhs: Expression);
}
*/

#[cfg(test)]
mod tests {

    use super::Expression::*;
    use crate::lexer::Token::*;

    #[test]
    fn test() {
        let expr = Factor(
            Star,
            Unary(Minus, Literal(Number(123f64)).into()).into(),
            Grouping(Literal(Number(45.67)).into()).into(),
        );

        assert_eq!(format!("{expr}"), "(* (- 123) (group 45.67))");
    }
}
