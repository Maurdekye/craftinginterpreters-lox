use std::{
    borrow::{Borrow, Cow},
    collections::{hash_map::Entry, HashMap},
    fmt::Display,
};

use polonius_the_crab::{exit_polonius, polonius, polonius_return};
use replace_with::replace_with_or_abort;

use crate::{
    lexer::Token,
    parser::{Expression, Statement},
    util::{AppendLocatedError, AsOwned, EntryInsert, Locateable, Located, LocatedAt},
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
    VarEvaluation(Box<Located<Error>>),
    #[error("In this print statement:\n{0}")]
    PrintEvaluation(Box<Located<Error>>),
    #[error("In this block:\n{0}")]
    BlockEvaluation(Box<Located<Error>>),
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

#[derive(Debug)]
pub enum Environment {
    Global(HashMap<String, Value>),
    Scope(HashMap<String, Value>, Box<Environment>),
}

impl Environment {
    pub fn new() -> Self {
        Self::Global(HashMap::new())
    }

    pub fn entry<'a>(&'a mut self, key: String) -> Entry<'a, String, Value> {
        let (mut env, outer_scope) = match self {
            Environment::Global(env) => return env.entry(key),
            Environment::Scope(env, outer_scope) => (env, outer_scope),
        };
        let key = polonius!(|env| -> Entry<'polonius, String, Value> {
            match env.entry(key) {
                entry @ Entry::Occupied(_) => polonius_return!(entry),
                Entry::Vacant(vacant) => exit_polonius!(vacant.into_key()),
            }
        });
        let key = match outer_scope.entry(key) {
            entry @ Entry::Occupied(_) => return entry,
            Entry::Vacant(vacant) => vacant.into_key(),
        };
        return env.entry(key);
    }

    pub fn top_entry(&mut self, key: String) -> Entry<'_, String, Value> {
        let (Environment::Global(env) | Environment::Scope(env, _)) = self;
        env.entry(key)
    }

    pub fn push(&mut self) {
        replace_with_or_abort(self, |old_self| {
            Environment::Scope(HashMap::new(), Box::new(old_self))
        })
    }

    pub fn pop(&mut self) -> Result<(), AtGlobalScopeError> {
        let mut result = Ok(());
        replace_with_or_abort(self, |old_self| match old_self {
            Environment::Global(_) => {
                result = Err(AtGlobalScopeError);
                old_self
            }
            Environment::Scope(_, outer_scope) => *outer_scope,
        });
        result
    }
}

#[derive(Clone, Debug, ThisError)]
#[error("Already at global scope")]
pub struct AtGlobalScopeError;

pub struct Interpreter {
    environment: Environment,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
        }
    }

    pub fn interpret(&mut self, statements: Vec<Located<Statement>>) -> Result<(), Located<Error>> {
        for statement in statements {
            self.statement(statement)?;
        }
        Ok(())
    }

    fn statement(&mut self, statement: Located<Statement>) -> Result<(), Located<Error>> {
        let location = statement.location();
        match statement.item {
            Statement::Print(expression) => {
                let result = self
                    .evaluate(expression)
                    .with_err_at(Error::PrintEvaluation, &location)?;
                let repr: Cow<'_, String> = match result.borrow() {
                    Value::String(s) => Cow::Borrowed(s),
                    value => Cow::Owned(format!("{value}")),
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
                        .with_err_at(Error::VarEvaluation, &location)?
                        .into_owned(), // own must occur in order to store the value
                    None => Value::Nil,
                };
                self.environment.top_entry(name).insert(value);
            }
            Statement::Block(statements) => {
                self.environment.push();
                let result = self
                    .block(statements)
                    .with_err_at(Error::BlockEvaluation, &location);
                self.environment
                    .pop()
                    .expect("Will always have just pushed a scope");
                result?;
            }
        }
        Ok(())
    }

    fn evaluate(&mut self, expression: Located<Expression>) -> Result<Cow<Value>, Located<Error>> {
        let location = expression.location();
        match expression.item {
            Expression::Literal(literal_token) => self
                .literal(literal_token)
                .as_owned()
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
                .as_owned()
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

    fn variable(&mut self, name: String) -> Result<Cow<Value>, String> {
        match self.environment.entry(name) {
            Entry::Occupied(occupied) => Ok(Cow::Borrowed(occupied.into_mut())),
            Entry::Vacant(vacant) => Err(vacant.into_key()),
        }
    }

    fn block(&mut self, statements: Vec<Located<Statement>>) -> Result<(), Located<Error>> {
        for statement in statements {
            self.statement(statement)?;
        }
        Ok(())
    }

    fn assignment<'a>(
        &'a mut self,
        name: Located<String>,
        expression: Located<Expression>,
    ) -> Result<Cow<'a, Value>, Located<Error>> {
        let (location, name) = name.split();
        let value = self.evaluate(expression)?.into_owned(); // own must occur in order to store the value
        match self.environment.entry(name) {
            Entry::Vacant(vacant) => {
                Err(Error::UndeclaredVariable(vacant.into_key()).at(&location))
            }
            Entry::Occupied(mut entry) => {
                entry.insert(value);
                Ok(Cow::Borrowed(entry.into_mut())) // everything is cows so that i can write this line here :)
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
        match (unary.item, value.borrow()) {
            (Token::Minus, Value::Number(value)) => Ok(Value::Number(-value)),
            (Token::Bang, Value::False | Value::Nil) => Ok(Value::True),
            (Token::Bang, Value::True) => Ok(Value::False),
            (unary, _) => Err(Error::InvalidUnary(unary, value.into_owned()).at(&location)), // error contents must be owned
        }
    }

    fn binary(
        &mut self,
        binary: Located<Token>,
        lhs_expr: Located<Expression>,
        rhs_expr: Located<Expression>,
    ) -> Result<Cow<Value>, Located<Error>> {
        let binary_location = binary.location();
        let lhs_location = lhs_expr.location();

        let lhs_value = self.evaluate(lhs_expr)?;

        // match short circuit boolean operations before evaluating right hand side
        let lhs_value = match (lhs_value.borrow(), &binary.item) {
            (Value::False | Value::Nil, Token::And) | (Value::True, Token::Or) => {
                return Ok(Cow::Owned(lhs_value.into_owned())); // this is a cheap own, because the value can only ever be False, True, or Nil
            }
            _ => lhs_value.into_owned(), // this own may not be cheap, but it is unavoidable, because we must also borrow rhs 😔
        };

        let rhs_value = self.evaluate(rhs_expr)?;

        match (lhs_value.borrow(), binary.item, rhs_value.borrow()) {
            // equality
            (lhs, Token::EqualEqual, rhs) => Ok(Cow::Owned((lhs == rhs).into())),
            (lhs, Token::BangEqual, rhs) => Ok(Cow::Owned((lhs != rhs).into())),

            // boolean
            (Value::True, Token::And, _) | (Value::False | Value::Nil, Token::Or, _) => {
                Ok(rhs_value)
            }

            // comparison
            (Value::Number(lhs), Token::Less, Value::Number(rhs)) => {
                Ok(Cow::Owned((lhs < rhs).into()))
            }
            (Value::Number(lhs), Token::LessEqual, Value::Number(rhs)) => {
                Ok(Cow::Owned((lhs <= rhs).into()))
            }
            (Value::Number(lhs), Token::Greater, Value::Number(rhs)) => {
                Ok(Cow::Owned((lhs > rhs).into()))
            }
            (Value::Number(lhs), Token::GreaterEqual, Value::Number(rhs)) => {
                Ok(Cow::Owned((lhs >= rhs).into()))
            }
            (Value::String(lhs), Token::Less, Value::String(rhs)) => {
                Ok(Cow::Owned((lhs < rhs).into()))
            }
            (Value::String(lhs), Token::LessEqual, Value::String(rhs)) => {
                Ok(Cow::Owned((lhs <= rhs).into()))
            }
            (Value::String(lhs), Token::Greater, Value::String(rhs)) => {
                Ok(Cow::Owned((lhs > rhs).into()))
            }
            (Value::String(lhs), Token::GreaterEqual, Value::String(rhs)) => {
                Ok(Cow::Owned((lhs >= rhs).into()))
            }

            // arithmetic
            (_, Token::Slash, Value::Number(rhs)) if rhs.borrow() == &0.0 => {
                Err(Error::DivisionByZero(lhs_value).at(&lhs_location))
            }
            (Value::Number(lhs), Token::Minus, Value::Number(rhs)) => {
                Ok(Cow::Owned(Value::Number(lhs - rhs)))
            }
            (Value::Number(lhs), Token::Plus, Value::Number(rhs)) => {
                Ok(Cow::Owned(Value::Number(lhs + rhs)))
            }
            (Value::Number(lhs), Token::Star, Value::Number(rhs)) => {
                Ok(Cow::Owned(Value::Number(lhs * rhs)))
            }
            (Value::Number(lhs), Token::Slash, Value::Number(rhs)) => {
                Ok(Cow::Owned(Value::Number(lhs / rhs)))
            }

            // string concatenation
            (Value::String(lhs), Token::Plus, Value::String(rhs)) => {
                Ok(Cow::Owned(Value::String(format!("{lhs}{rhs}"))))
            }
            (Value::String(lhs), Token::Plus, rhs) => {
                Ok(Cow::Owned(Value::String(format!("{lhs}{rhs}"))))
            }
            (lhs, Token::Plus, Value::String(rhs)) => {
                Ok(Cow::Owned(Value::String(format!("{lhs}{rhs}"))))
            }

            // string cycling
            (Value::String(string), Token::Star, Value::Number(quantity))
            | (Value::Number(quantity), Token::Star, Value::String(string)) => {
                Ok(Cow::Owned(Value::String(string.repeat(*quantity as usize))))
            }

            // invalid
            (_, operator, _) => {
                Err(
                    Error::InvalidBinary(lhs_value, operator, rhs_value.into_owned())
                        .at(&binary_location),
                ) // error contents must be owned
            }
        }
    }

    fn ternary(
        &mut self,
        condition_expr: Located<Expression>,
        true_branch_expr: Located<Expression>,
        false_branch_expr: Located<Expression>,
    ) -> Result<Cow<Value>, Located<Error>> {
        let condition_location = condition_expr.location();

        let condition_value = self.evaluate(condition_expr)?;
        let condition_bool = match condition_value.borrow() {
            Value::True => true,
            Value::False => false,
            _ => {
                return Err(
                    Error::InvalidTernary(condition_value.into_owned()).at(&condition_location)
                )
            } // error contents must be owned
        };

        if condition_bool {
            self.evaluate(true_branch_expr)
        } else {
            self.evaluate(false_branch_expr)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Environment, Value};

    #[test]
    fn test() {
        let mut env = Environment::new();
        env.entry("x".to_string()).or_insert(Value::Number(5.0));
        env.entry("y".to_string()).or_insert(Value::Number(10.0));
        env.push();
        env.entry("x".to_string())
            .and_modify(|x| *x = Value::Number(40.0));
        env.entry("z".to_string()).or_insert(Value::Number(607.0));
        dbg!(&env);
        env.top_entry("x".to_string())
            .or_insert(Value::Number(900.0));
        dbg!(&env);
        env.pop().unwrap();
        env.entry("x".to_string())
            .and_modify(|x| *x = Value::Number(18.0));
        dbg!(&env);
    }
}
