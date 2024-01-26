use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Display,
};

use crate::{
    lexer::Token,
    parser::{Expression, Statement},
    util::{AppendLocatedError, Locateable, Located, LocatedAt},
};

use thiserror::Error as ThisError;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("In this assignment:\n{0}")]
    AssignmentEvaluation(Box<Located<Error>>),
    #[error("At this unary operator:\n{0}")]
    UnaryEvaluation(Box<Located<Error>>),
    #[error("In this binary expression:\n{0}")]
    BinaryEvaluation(Box<Located<Error>>),
    #[error("In this ternary:\n{0}")]
    TernaryEvaluation(Box<Located<Error>>),

    #[error("In this var statement:\n{0}")]
    VarStatementEvaluation(Box<Located<Error>>),
    #[error("In this print statement:\n{0}")]
    PrintStatementEvaluation(Box<Located<Error>>),
    #[error("In this statement:\n{0}")]
    ExpressionStatementEvaluation(Box<Located<Error>>),

    #[error("You haven't defined '{0}' yet")]
    UndeclaredVariable(String),
    #[error("I can't '{0}' a '{1}'")]
    InvalidUnary(Token, Value),
    #[error("I can't '{1}' a '{0}' and a '{2}'")]
    InvalidBinary(Value, Token, Value),
    #[error("Divided '{0}' by zero!")]
    DivisionByZero(Value),
    #[error("This is supposed to be true or false, but it was '{0}'")]
    InvalidTernary(Value),
    #[error("This is supposed to be a value, but it was a '{0}'")]
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
            Statement::Var(name, maybe_initializer) => {
                let value = match maybe_initializer {
                    Some(expression) => self
                        .evaluate(expression)
                        .with_err_at(Error::VarStatementEvaluation, &location)?,
                    None => Value::Nil,
                };
                self.environment.insert(name, value);
            }
        }
        Ok(Value::Nil)
    }

    fn evaluate(&mut self, expression: Located<Expression>) -> Result<Value, Located<Error>> {
        let location = expression.location();
        match expression.item {
            Expression::Literal(literal_token) => self
                .literal(literal_token)
                .with_err_at(Error::InvalidLiteral, &location),
            Expression::Variable(name) => self
                .variable(name)
                .with_err_at(Error::UndeclaredVariable, &location),
            Expression::Assignment(name, sub_expression) => self
                .assignment(name, sub_expression.as_deref())
                .with_err_at(Error::AssignmentEvaluation, &location),
            Expression::Grouping(sub_expression) => self.evaluate(sub_expression.as_deref()),
            Expression::Unary(unary_operator, unary_expr) => self
                .unary(unary_operator, unary_expr.as_deref())
                .with_err_at(Error::UnaryEvaluation, &location),
            Expression::Binary(binary_operator, lhs_expr, rhs_expr) => self
                .binary(binary_operator, lhs_expr.as_deref(), rhs_expr.as_deref())
                .with_err_at(Error::BinaryEvaluation, &location),
            Expression::Ternary(condition_expr, true_branch_expr, false_branch_expr) => self
                .ternary(
                    condition_expr.as_deref(),
                    true_branch_expr.as_deref(),
                    false_branch_expr.as_deref(),
                )
                .with_err_at(Error::TernaryEvaluation, &location),
        }
    }

    fn literal(&mut self, literal: Located<Token>) -> Result<Value, Token> {
        literal.item.try_into()
    }

    fn variable(&mut self, name: String) -> Result<Value, String> {
        self.environment.get(&name).cloned().ok_or(name)
    }

    fn assignment(
        &mut self,
        name: Located<String>,
        expression: Located<Expression>,
    ) -> Result<Value, Located<Error>> {
        let (location, name) = name.split();
        let value = self.evaluate(expression)?;
        match self.environment.entry(name.clone()) {
            Entry::Vacant(_) => Err(Error::UndeclaredVariable(name).at(&location)),
            Entry::Occupied(mut entry) => {
                entry.insert(value.clone());
                Ok(value)
            }
        }
    }

    fn unary(
        &mut self,
        unary: Located<Token>,
        unary_expr: Located<Expression>,
    ) -> Result<Value, Located<Error>> {
        let location = unary.location();
        let value = self.evaluate(unary_expr)?;
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

        let lhs_value = self.evaluate(lhs_expr)?;

        // match short circuit boolean operations before evaluating right hand side
        let lhs_value = match (lhs_value, &binary.item) {
            (lhs @ (Value::False | Value::Nil), Token::And) | (lhs @ Value::True, Token::Or) => {
                return Ok(lhs)
            }
            (lhs, _) => lhs,
        };

        let rhs_value = self.evaluate(rhs_expr)?;

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

            // string cycling
            (Value::String(string), Token::Star, Value::Number(quantity))
            | (Value::Number(quantity), Token::Star, Value::String(string)) => {
                Ok(Value::String(string.repeat(quantity as usize)))
            }

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

        let condition_value = self.evaluate(condition_expr)?;
        let condition_bool = match condition_value {
            Value::True => true,
            Value::False => false,
            value => return Err(Error::InvalidTernary(value).at(&condition_location)),
        };

        if condition_bool {
            self.evaluate(true_branch_expr)
        } else {
            self.evaluate(false_branch_expr)
        }
    }
}
