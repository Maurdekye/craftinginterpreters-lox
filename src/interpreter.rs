use std::{fmt::Display, iter::once};

use crate::{
    lexer::Token,
    parser::Expression,
    util::{Errors, Locateable, Located, LocatedAt},
};

use thiserror::Error as ThisError;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Error evaluating unary expression:\n{0}")]
    UnaryEvaluation(Box<Located<Error>>),
    #[error("Error evaluating left hand side of binary expression:\n{0}")]
    BinaryLeftEvaluation(Box<Located<Error>>),
    #[error("Error evaluating right hand side of binary expression:\n{0}")]
    BinaryRightEvaluation(Box<Located<Error>>),
    #[error("Error evaluating condition of ternary expression:\n{0}")]
    TernaryConditionEvaluation(Box<Located<Error>>),
    #[error("Error evaluating true branch of ternary expression:\n{0}")]
    TernaryTrueBranchEvaluation(Box<Located<Error>>),
    #[error("Error evaluating false branch of ternary expression:\n{0}")]
    TernaryFalseBranchEvaluation(Box<Located<Error>>),
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

impl TryFrom<Token> for Value {
    type Error = Token;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::String(s) => Ok(Value::String(s)),
            Token::Number(n) => Ok(Value::Number(n)),
            Token::True => Ok(Value::True),
            Token::False => Ok(Value::False),
            Token::Nil => Ok(Value::Nil),
            value => Err(value),
        }
    }
}

pub struct Interpreter;

impl Interpreter {
    pub fn new() -> Self {
        Self
    }

    pub fn interpret(
        &mut self,
        expression: Located<Expression>,
    ) -> Result<Value, Errors<Located<Error>>> {
        self.evaluate(expression).map_err(|e| once(e).collect())
    }

    pub fn evaluate(&mut self, expression: Located<Expression>) -> Result<Value, Located<Error>> {
        match expression.item {
            Expression::Literal(literal_token) => self.literal(literal_token),
            Expression::Grouping(sub_expression) => self.evaluate(sub_expression.as_deref()),
            Expression::Unary(unary_operator, unary_expr) => {
                self.unary(unary_operator, unary_expr.as_deref())
            }
            Expression::Binary(binary_operator, lhs_expr, rhs_expr) => {
                self.binary(binary_operator, lhs_expr.as_deref(), rhs_expr.as_deref())
            }
            Expression::Ternary(condition_expr, true_branch_expr, false_branch_expr) => self
                .ternary(
                    condition_expr.as_deref(),
                    true_branch_expr.as_deref(),
                    false_branch_expr.as_deref(),
                ),
        }
    }

    fn literal(&mut self, literal: Located<Token>) -> Result<Value, Located<Error>> {
        let location = literal.location();
        literal
            .item
            .try_into()
            .map_err(|value: Token| Error::InvalidLiteral(value).at(&location))
    }

    fn unary(
        &mut self,
        unary: Located<Token>,
        unary_expr: Located<Expression>,
    ) -> Result<Value, Located<Error>> {
        let location = unary.location();
        let value = self
            .evaluate(unary_expr)
            .map_err(|err| Error::UnaryEvaluation(err.into()).at(&location))?;
        match (unary.item, value) {
            (Token::Minus, Value::Number(value)) => Ok(Value::Number(-value)),
            (Token::Bang, Value::False) => Ok(Value::True),
            (Token::Bang, Value::True) => Ok(Value::False),
            (unary, value) => Err(Error::InvalidUnary(unary, value).at(&location)),
        }
    }

    fn binary(
        &mut self,
        binary: Located<Token>,
        lhs_expr: Located<Expression>,
        rhs_expr: Located<Expression>,
    ) -> Result<Value, Located<Error>> {
        let binary_location = binary.location();
        let lhs_location = lhs_expr.location();
        let rhs_location = rhs_expr.location();
        let lhs_value = self
            .evaluate(lhs_expr)
            .map_err(|err| Error::BinaryLeftEvaluation(err.into()).at(&lhs_location))?;
        // match short circuit boolean operations
        let lhs_value = match (lhs_value, &binary.item) {
            (lhs @ Value::False, Token::And) | (lhs @ Value::True, Token::Or) => return Ok(lhs),
            (lhs, _) => lhs,
        };
        let rhs_value = self
            .evaluate(rhs_expr)
            .map_err(|err| Error::BinaryRightEvaluation(err.into()).at(&rhs_location))?;
        match (lhs_value, binary.item, rhs_value) {
            (lhs, Token::EqualEqual, rhs) => Ok(self.compare(lhs, rhs).into()),
            (lhs, Token::BangEqual, rhs) => Ok((!self.compare(lhs, rhs)).into()),
            (Value::True, Token::And, rhs) | (Value::False, Token::Or, rhs) => Ok(rhs),
            (Value::Number(lhs), Token::Less, Value::Number(rhs)) => Ok((lhs < rhs).into()),
            (Value::Number(lhs), Token::LessEqual, Value::Number(rhs)) => Ok((lhs <= rhs).into()),
            (Value::Number(lhs), Token::Greater, Value::Number(rhs)) => Ok((lhs > rhs).into()),
            (Value::Number(lhs), Token::GreaterEqual, Value::Number(rhs)) => {
                Ok((lhs >= rhs).into())
            }
            (Value::Number(lhs), Token::Minus, Value::Number(rhs)) => Ok(Value::Number(lhs - rhs)),
            (Value::Number(lhs), Token::Plus, Value::Number(rhs)) => Ok(Value::Number(lhs + rhs)),
            (Value::Number(lhs), Token::Star, Value::Number(rhs)) => Ok(Value::Number(lhs * rhs)),
            (Value::Number(lhs), Token::Slash, Value::Number(rhs)) => Ok(Value::Number(lhs / rhs)),
            (lhs, operator, rhs) => {
                Err(Error::InvalidBinary(operator, lhs, rhs).at(&binary_location))
            }
        }
    }

    fn compare(&mut self, lhs: Value, rhs: Value) -> bool {
        match (lhs, rhs) {
            (Value::True, Value::True) | (Value::False, Value::False) => true,
            (Value::Nil, Value::Nil) => true,
            (Value::String(lhs), Value::String(rhs)) => lhs == rhs,
            (Value::Number(lhs), Value::Number(rhs)) => lhs == rhs,
            _ => false,
        }
    }

    fn ternary(
        &mut self,
        condition_expr: Located<Expression>,
        true_branch_expr: Located<Expression>,
        false_branch_expr: Located<Expression>,
    ) -> Result<Value, Located<Error>> {
        let condition_location = condition_expr.location();
        let true_branch_location = true_branch_expr.location();
        let false_branch_location = false_branch_expr.location();
        let condition_value = self
            .evaluate(condition_expr)
            .map_err(|err| Error::TernaryConditionEvaluation(err.into()).at(&condition_location))?;
        let condition_bool = match condition_value {
            Value::True => true,
            Value::False => false,
            value => return Err(Error::InvalidTernary(value).at(&condition_location)),
        };
        if condition_bool {
            self.evaluate(true_branch_expr).map_err(|err| {
                Error::TernaryTrueBranchEvaluation(err.into()).at(&true_branch_location)
            })
        } else {
            self.evaluate(false_branch_expr).map_err(|err| {
                Error::TernaryFalseBranchEvaluation(err.into()).at(&false_branch_location)
            })
        }
    }
}
