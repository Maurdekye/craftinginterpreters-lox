use std::{fmt::Display, iter::once};

use crate::{
    lexer::Token,
    parser::Expression,
    util::{Errors, Located, Location, MaybeLocated, MaybeLocatedAt},
};

use thiserror::Error as ThisError;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Error evaluating unary expression:\n{0}")]
    UnaryEvaluation(Box<MaybeLocated<Error>>),
    #[error("Error evaluating left hand side of binary expression:\n{0}")]
    BinaryLeftEvaluation(Box<MaybeLocated<Error>>),
    #[error("Error evaluating right hand side of binary expression:\n{0}")]
    BinaryRightEvaluation(Box<MaybeLocated<Error>>),
    #[error("Error evaluating condition of ternary expression:\n{0}")]
    TernaryConditionEvaluation(Box<MaybeLocated<Error>>),
    #[error("Error evaluating true branch of ternary expression:\n{0}")]
    TernaryTrueBranchEvaluation(Box<MaybeLocated<Error>>),
    #[error("Error evaluating false branch of ternary expression:\n{0}")]
    TernaryFalseBranchEvaluation(Box<MaybeLocated<Error>>),
    #[error("Invalid unary '{0}' on value '{1}'")]
    InvalidUnary(Token, Value),
    #[error("Invalid binary '{0}' between values '{1}' and '{2}'")]
    InvalidBinary(Token, Value, Value),
    #[error("Invalid ternary condtion: expected boolean, found '{0}'")]
    InvalidTernary(Value),
    #[error("Expected literal, found '{0}'")]
    InvalidLiteral(Token),
}

#[derive(Clone, Debug)]
pub enum Value {
    String(String),
    Number(f64),
    True,
    False,
    Nil,
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        if value {
            Self::True
        } else {
            Self::False
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{s}\""),
            Value::Number(n) => write!(f, "{n}"),
            Value::True => write!(f, "true"),
            Value::False => write!(f, "false"),
            Value::Nil => write!(f, "nil"),
        }
    }
}

pub fn interpret(expression: Expression) -> Result<Value, Errors<MaybeLocated<Error>>> {
    evaluate(expression).map_err(|e| once(e).collect())
}

pub fn evaluate(expression: Expression) -> Result<Value, MaybeLocated<Error>> {
    match expression {
        Expression::Literal(literal_token) => literal(literal_token),
        Expression::Grouping(sub_expression) => evaluate(*sub_expression),
        Expression::Unary(unary_operator, unary_expr) => unary(unary_operator, *unary_expr),
        Expression::Binary(binary_operator, lhs_expr, rhs_expr) => {
            binary(binary_operator, *lhs_expr, *rhs_expr)
        }
        Expression::Ternary(condition_expr, true_branch_expr, false_branch_expr) => {
            ternary(*condition_expr, *true_branch_expr, *false_branch_expr)
        }
    }
}

fn literal(literal: Located<Token>) -> Result<Value, MaybeLocated<Error>> {
    match literal.item {
        Token::String(s) => Ok(Value::String(s)),
        Token::Number(n) => Ok(Value::Number(n)),
        Token::True => Ok(Value::True),
        Token::False => Ok(Value::False),
        Token::Nil => Ok(Value::Nil),
        _ => {
            let location = Location::from(&literal);
            Err(Error::InvalidLiteral(literal.item).located_at(&location))
        }
    }
}

fn unary(unary: Located<Token>, unary_expr: Expression) -> Result<Value, MaybeLocated<Error>> {
    let location = Location::from(&unary);
    let value = evaluate(unary_expr)
        .map_err(|err| Error::UnaryEvaluation(err.into()).located_at(&location))?;
    match (unary.item, value) {
        (Token::Minus, Value::Number(value)) => Ok(Value::Number(-value)),
        (Token::Bang, Value::False) => Ok(Value::True),
        (Token::Bang, Value::True) => Ok(Value::False),
        (unary, value) => Err(Error::InvalidUnary(unary, value).located_at(&location)),
    }
}

fn binary(
    binary: Located<Token>,
    lhs_expr: Expression,
    rhs_expr: Expression,
) -> Result<Value, MaybeLocated<Error>> {
    let location = Location::from(&binary);
    let lhs_value = evaluate(lhs_expr)
        .map_err(|err| Error::BinaryLeftEvaluation(err.into()).located_at(&location))?;
    let rhs_value = evaluate(rhs_expr)
        .map_err(|err| Error::BinaryRightEvaluation(err.into()).located_at(&location))?;
    match (lhs_value, binary.item, rhs_value) {
        (lhs, Token::EqualEqual, rhs) => Ok(compare(lhs, rhs).into()),
        (lhs, Token::BangEqual, rhs) => Ok((!compare(lhs, rhs)).into()),
        (Value::Number(lhs), Token::Less, Value::Number(rhs)) => Ok((lhs < rhs).into()),
        (Value::Number(lhs), Token::LessEqual, Value::Number(rhs)) => Ok((lhs <= rhs).into()),
        (Value::Number(lhs), Token::Greater, Value::Number(rhs)) => Ok((lhs > rhs).into()),
        (Value::Number(lhs), Token::GreaterEqual, Value::Number(rhs)) => Ok((lhs >= rhs).into()),
        (Value::Number(lhs), Token::Minus, Value::Number(rhs)) => Ok(Value::Number(lhs - rhs)),
        (Value::Number(lhs), Token::Plus, Value::Number(rhs)) => Ok(Value::Number(lhs + rhs)),
        (Value::Number(lhs), Token::Star, Value::Number(rhs)) => Ok(Value::Number(lhs * rhs)),
        (Value::Number(lhs), Token::Slash, Value::Number(rhs)) => Ok(Value::Number(lhs / rhs)),
        (lhs, operator, rhs) => Err(Error::InvalidBinary(operator, lhs, rhs).located_at(&location)),
    }
}

fn compare(lhs: Value, rhs: Value) -> bool {
    match (lhs, rhs) {
        (Value::True, Value::True) | (Value::False, Value::False) => true,
        (Value::Nil, Value::Nil) => true,
        (Value::String(lhs), Value::String(rhs)) => lhs == rhs,
        (Value::Number(lhs), Value::Number(rhs)) => lhs == rhs,
        _ => false,
    }
}

fn ternary(
    condition_expr: Expression,
    true_branch_expr: Expression,
    false_branch_expr: Expression,
) -> Result<Value, MaybeLocated<Error>> {
    let condition_value = evaluate(condition_expr)
        .map_err(|err| Error::TernaryConditionEvaluation(err.into()).unlocated())?;
    let condition_bool = match condition_value {
        Value::True => true,
        Value::False => false,
        value => return Err(Error::InvalidTernary(value).unlocated()),
    };
    if condition_bool {
        evaluate(true_branch_expr)
            .map_err(|err| Error::TernaryTrueBranchEvaluation(err.into()).unlocated())
    } else {
        evaluate(false_branch_expr)
            .map_err(|err| Error::TernaryFalseBranchEvaluation(err.into()).unlocated())
    }
}
