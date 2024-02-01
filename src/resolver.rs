use std::collections::HashMap;

use crate::{
    interpreter::Interpreter,
    parser::{Expression, Statement},
    util::{Locateable, Located, LocatedAt, Location},
};

use thiserror::Error as ThisError;

macro_rules! split_ref {
    ($located:expr => |$item:ident, $location:ident| $body:block) => {{
        let located = $located;
        let $location = located.location();
        let $item = &located.item;
        $body
    }};
    ($located:expr => |$item:ident, _| $body:block) => {{
        let located = $located;
        let $item = &located.item;
        $body
    }};
}

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Can't read local variable in its own initializer")]
    VariableReadDuringInitialize,
}

pub struct Resolver<'a> {
    scopes: Vec<HashMap<String, bool>>,
    interpreter: &'a mut Interpreter,
}

type ResolverResult = Result<(), Located<Error>>;

impl<'a> Resolver<'a> {
    pub fn new(interpreter: &'a mut Interpreter) -> Self {
        Self {
            scopes: Vec::new(),
            interpreter: interpreter,
        }
    }

    pub fn resolve(&mut self, statements: &Vec<Located<Statement>>) -> ResolverResult {
        for statement in statements {
            self.statement(statement)?;
        }
        Ok(())
    }

    fn set_value(&mut self, name: String, value: bool) {
        self.scopes
            .last_mut()
            .map(|s| s.insert(name.clone(), value));
    }

    fn statement(&mut self, statement: &Located<Statement>) -> ResolverResult {
        split_ref!(statement => |statement, _| {
            match statement {
                Statement::Block(statements) => {
                    self.scopes.push(HashMap::new());
                    self.resolve(statements)?;
                    self.scopes.pop();
                }
                Statement::Var(name, initializer) => {
                    self.set_value(name.clone(), false);
                    if let Some(initializer) = initializer {
                        self.expression(initializer)?;
                    }
                    self.set_value(name.clone(), true);
                }
                Statement::Function(name, parameters, body) => {
                    self.set_value(name.item.clone(), true);
                    self.function(parameters, body.as_ref())?;
                }
                Statement::Expression(expression)
                | Statement::Print(expression)
                | Statement::Return(Some(expression)) => {
                    self.expression(expression)?;
                }
                Statement::If(condition, true_branch, false_branch) => {
                    self.expression(condition)?;
                    self.statement(true_branch)?;
                    if let Some(false_branch) = false_branch.as_ref() {
                        self.statement(false_branch)?;
                    }
                }
                Statement::While(condition, body) => {
                    self.expression(condition)?;
                    self.statement(body)?;
                }
                Statement::Break
                | Statement::Continue
                | Statement::Return(None) => (),
            }
        });
        Ok(())
    }

    pub fn expression(&mut self, expression: &Located<Expression>) -> ResolverResult {
        split_ref!(expression => |expression, location| {
            match expression {
                Expression::Variable(name) => {
                    if self.scopes.last_mut().and_then(|s| s.get(name)).map(|s| !*s).unwrap_or(false) {
                        return Err(Error::VariableReadDuringInitialize.at(&location));
                    }
                    self.resolve_local(name, location)?;
                }
                Expression::Assignment(name, value_expression) => {
                    self.expression(value_expression.as_ref())?;
                    self.resolve_local(&name.item, location)?;
                }
                Expression::Binary(_, lhs_expression, rhs_expression) => {
                    self.expression(lhs_expression)?;
                    self.expression(rhs_expression)?;
                }
                Expression::Call(callee, arguments) => {
                    self.expression(callee)?;
                    for arg in arguments {
                        self.expression(arg)?;
                    }
                }
                Expression::Grouping(expression)
                | Expression::Unary(_, expression) => {
                    self.expression(expression)?;
                },
                Expression::Ternary(condition, true_expression, false_expression) => {
                    self.expression(condition)?;
                    self.expression(true_expression)?;
                    self.expression(false_expression)?;
                },
                Expression::Lambda(parameters, body) => {
                    self.function(parameters, body.as_ref())?;
                },
                Expression::Literal(_) => (),
            }
        });
        Ok(())
    }

    fn function(
        &mut self,
        parameters: &Vec<Located<String>>,
        body: &Located<Statement>,
    ) -> ResolverResult {
        self.scopes.push(HashMap::new());
        for parameter in parameters.iter() {
            self.set_value(parameter.item.clone(), true);
        }
        self.statement(body)?;
        self.scopes.pop();
        Ok(())
    }

    fn resolve_local(&mut self, name: &String, location: Location) -> ResolverResult {
        for (i, scope) in self.scopes.iter().rev().enumerate() {
            if scope.contains_key(name) {
                self.interpreter.resolve(location, i);
                break;
            }
        }
        Ok(())
    }
}
