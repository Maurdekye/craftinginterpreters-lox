use std::{collections::HashMap, fmt::Display};

use crate::{
    lexer::Token,
    parser::{Expression, Statement},
    util::{AppendLocatedError, Locateable, Located, LocatedAt},
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

    #[error("Error evaluating print statement:\n{0}")]
    PrintStatementEvaluation(Box<Located<Error>>),
    #[error("Error evaluating expression statement:\n{0}")]
    ExpressionStatementEvaluation(Box<Located<Error>>),
    #[error("Error evaluating variable declaration:\n{0}")]
    VarStatementEvaluation(Box<Located<Error>>),

    #[error("Attempt to reference undeclared variable '{0}'")]
    UndeclaredVariable(String),
    #[error("Invalid unary '{0}' on value '{1}'")]
    InvalidUnary(Token, Value),
    #[error("Invalid binary '{1}' between values '{0}' and '{2}'")]
    InvalidBinary(Value, Token, Value),
    #[error("Attempt to divide '{0}' by zero")]
    DivisionByZero(Value),
    #[error("Invalid ternary condtion: expected boolean, found '{0}'")]
    InvalidTernary(Value),
    #[error("Expected literal, found '{0}'")]
    InvalidLiteral(Token),
}

#[derive(Clone, Debug, PartialEq)]
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

pub struct Interpreter {
    environment: HashMap<String, Value>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            environment: HashMap::new(),
        }
    }

    /// The signature is set up to support statements *potentially* evaluating to a
    /// value in future versions of the code, but currently, they always evaluate to Nil.
    pub fn interpret(
        &mut self,
        statements: Vec<Located<Statement>>,
    ) -> Result<Value, Located<Error>> {
        let mut result = Value::Nil;
        for statement in statements {
            result = self.statement(statement)?;
        }
        Ok(result)
    }

    fn statement(&mut self, statement: Located<Statement>) -> Result<Value, Located<Error>> {
        let location = statement.location();
        match statement.item {
            Statement::Print(expression) => {
                let result = self
                    .evaluate(expression)
                    .with_err_at(Error::PrintStatementEvaluation, &location)?;
                let repr = match result {
                    Value::String(s) => s,
                    value => format!("{value}"),
                };
                println!("{repr}");
            }
            Statement::Expression(expression) => {
                self.evaluate(expression)
                    .with_err_at(Error::ExpressionStatementEvaluation, &location)?;
            }
            Statement::Var(name, expression) => {
                let value = self
                    .evaluate(expression)
                    .with_err_at(Error::VarStatementEvaluation, &location)?;
                self.environment.insert(name, value);
            }
        }
        Ok(Value::Nil)
    }

    fn evaluate(&mut self, expression: Located<Expression>) -> Result<Value, Located<Error>> {
        let location = expression.location();
        match expression.item {
            Expression::Literal(literal_token) => self.literal(literal_token),
            Expression::Variable(name) => self
                .environment
                .get(&name)
                .cloned()
                .ok_or_else(|| Error::UndeclaredVariable(name).at(&location)),
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
            .with_err_at(Error::InvalidLiteral, &location)
    }

    fn unary(
        &mut self,
        unary: Located<Token>,
        unary_expr: Located<Expression>,
    ) -> Result<Value, Located<Error>> {
        let location = unary.location();
        let value = self
            .evaluate(unary_expr)
            .with_err_at(Error::UnaryEvaluation, &location)?;
        match (unary.item, value) {
            (Token::Minus, Value::Number(value)) => Ok(Value::Number(-value)),
            (Token::Bang, Value::False | Value::Nil) => Ok(Value::True),
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
            .with_err_at(Error::BinaryLeftEvaluation, &lhs_location)?;

        // match short circuit boolean operations before evaluating right hand side
        let lhs_value = match (lhs_value, &binary.item) {
            (lhs @ (Value::False | Value::Nil), Token::And) | (lhs @ Value::True, Token::Or) => {
                return Ok(lhs)
            }
            (lhs, _) => lhs,
        };

        let rhs_value = self
            .evaluate(rhs_expr)
            .with_err_at(Error::BinaryRightEvaluation, &rhs_location)?;

        match (lhs_value, binary.item, rhs_value) {
            // equality
            (lhs, Token::EqualEqual, rhs) => Ok((lhs == rhs).into()),
            (lhs, Token::BangEqual, rhs) => Ok((lhs != rhs).into()),

            // boolean
            (Value::True, Token::And, rhs) | (Value::False | Value::Nil, Token::Or, rhs) => Ok(rhs),

            // comparison
            (Value::Number(lhs), Token::Less, Value::Number(rhs)) => Ok((lhs < rhs).into()),
            (Value::Number(lhs), Token::LessEqual, Value::Number(rhs)) => Ok((lhs <= rhs).into()),
            (Value::Number(lhs), Token::Greater, Value::Number(rhs)) => Ok((lhs > rhs).into()),
            (Value::Number(lhs), Token::GreaterEqual, Value::Number(rhs)) => {
                Ok((lhs >= rhs).into())
            }
            (Value::String(lhs), Token::Less, Value::String(rhs)) => Ok((lhs < rhs).into()),
            (Value::String(lhs), Token::LessEqual, Value::String(rhs)) => Ok((lhs <= rhs).into()),
            (Value::String(lhs), Token::Greater, Value::String(rhs)) => Ok((lhs > rhs).into()),
            (Value::String(lhs), Token::GreaterEqual, Value::String(rhs)) => {
                Ok((lhs >= rhs).into())
            }

            // arithmetic
            (lhs, Token::Slash, Value::Number(rhs)) if rhs == 0.0 => {
                Err(Error::DivisionByZero(lhs).at(&lhs_location))
            }
            (Value::Number(lhs), Token::Minus, Value::Number(rhs)) => Ok(Value::Number(lhs - rhs)),
            (Value::Number(lhs), Token::Plus, Value::Number(rhs)) => Ok(Value::Number(lhs + rhs)),
            (Value::Number(lhs), Token::Star, Value::Number(rhs)) => Ok(Value::Number(lhs * rhs)),
            (Value::Number(lhs), Token::Slash, Value::Number(rhs)) => Ok(Value::Number(lhs / rhs)),

            // string concatenation
            (Value::String(lhs), Token::Plus, Value::String(rhs)) => {
                Ok(Value::String(format!("{lhs}{rhs}")))
            }
            (Value::String(lhs), Token::Plus, rhs) => Ok(Value::String(format!("{lhs}{rhs}"))),
            (lhs, Token::Plus, Value::String(rhs)) => Ok(Value::String(format!("{lhs}{rhs}"))),

            // invalid
            (lhs, operator, rhs) => {
                Err(Error::InvalidBinary(lhs, operator, rhs).at(&binary_location))
            }
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
            .with_err_at(Error::TernaryConditionEvaluation, &condition_location)?;
        let condition_bool = match condition_value {
            Value::True => true,
            Value::False => false,
            value => return Err(Error::InvalidTernary(value).at(&condition_location)),
        };

        if condition_bool {
            self.evaluate(true_branch_expr)
                .with_err_at(Error::TernaryTrueBranchEvaluation, &true_branch_location)
        } else {
            self.evaluate(false_branch_expr)
                .with_err_at(Error::TernaryFalseBranchEvaluation, &false_branch_location)
        }
    }
}
