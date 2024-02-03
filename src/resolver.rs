use std::{collections::HashMap, hash::Hash};

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
    #[error("Can't return outside of a function")]
    ReturnFromOutsideFunction,
    #[error("Can't break outside of a loop")]
    BreakFromOutsideLoop,
    #[error("Can't continue outside of a loop")]
    ContinueFromOutsideLoop,
    #[error("Variable '{0}' is undefined")]
    UndefinedVariable(String),
    #[error("Declaration '{0}' is unused")]
    UnusedDeclaration(String),
}

enum FunctionType {
    None,
    Function,
}

enum LoopType {
    None,
    Loop,
}

#[derive(Debug, PartialEq, Eq)]
enum VarState {
    Declared,
    Defined,
    Used,
}

pub struct ReferenceId {
    path: Vec<usize>,
    identifier: String,
}

pub struct Resolver<'a> {
    scopes: Vec<HashMap<String, Located<VarState>>>,
    scope_ids: Vec<usize>,
    interpreter: &'a mut Interpreter,
    function_type: FunctionType,
    loop_type: LoopType,
}

type ResolverResult = Result<(), Located<Error>>;

impl<'a> Resolver<'a> {
    pub fn new(interpreter: &'a mut Interpreter) -> Self {
        Self {
            scopes: Vec::new(),
            scope_ids: Vec::new(),
            interpreter: interpreter,
            function_type: FunctionType::None,
            loop_type: LoopType::None,
        }
    }

    pub fn resolve(&mut self, statements: &Vec<Located<Statement>>) -> ResolverResult {
        self.push_scope()?;
        for statement in statements {
            self.statement(statement)?;
        }
        self.pop_scope()
    }

    fn set_value(&mut self, name: String, value: Located<VarState>) {
        self.scopes
            .last_mut()
            .map(|s| s.insert(name.clone(), value));
    }

    fn statement(&mut self, statement: &Located<Statement>) -> ResolverResult {
        split_ref!(statement => |statement, location| {
            match statement {
                Statement::Block(statements) => {
                    self.resolve(statements)?;
                }
                Statement::Var(name, initializer) => {
                    self.resolve_declaration(name.clone(), location.clone(), VarState::Declared)?;
                    if let Some(initializer) = initializer {
                        self.expression(initializer)?;
                    }
                    self.set_value(name.clone(), VarState::Defined.at(&location));
                }
                Statement::Function(name, parameters, body) => {
                    self.resolve_declaration(name.item.clone(), location.clone(), VarState::Defined)?;
                    self.function(parameters, body.as_ref(), FunctionType::Function, &location)?;
                }
                Statement::Expression(expression)
                | Statement::Print(expression) => {
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
                    let enclosing_type = std::mem::replace(&mut self.loop_type, LoopType::Loop);
                    self.expression(condition)?;
                    self.statement(body)?;
                    self.loop_type = enclosing_type;
                }
                Statement::Break => {
                    if let LoopType::None = self.loop_type {
                        return Err(Error::BreakFromOutsideLoop.at(&location))
                    }
                }
                Statement::Continue => {
                    if let LoopType::None = self.loop_type {
                        return Err(Error::ContinueFromOutsideLoop.at(&location))
                    }
                }
                Statement::Return(expression) => {
                    if let FunctionType::None = self.function_type {
                        return Err(Error::ReturnFromOutsideFunction.at(&location))
                    }
                    if let Some(expression) = expression {
                        self.expression(expression)?;
                    }
                }
            }
        });
        Ok(())
    }

    fn resolve_declaration(
        &mut self,
        name: String,
        location: Location,
        state: VarState,
    ) -> ResolverResult {
        self.variable_ids
            .insert((name.clone(), self.scopes.len()), self.variable_ids.len());
        self.set_value(name.clone(), state.at(&location));
        Ok(())
    }

    pub fn expression(&mut self, expression: &Located<Expression>) -> ResolverResult {
        split_ref!(expression => |expression, location| {
            match expression {
                Expression::Variable(name) => {
                    if self.scopes.last_mut().and_then(|s| s.get(name)).map(|s| s.item == VarState::Declared).unwrap_or(false) {
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
                    self.function(parameters, body.as_ref(), FunctionType::Function, &location)?;
                },
                Expression::Literal(_) => (),
            }
        });
        Ok(())
    }

    fn push_scope(&mut self) -> ResolverResult {
        self.scopes.push(HashMap::new());
        if self.scope_ids.len() < self.scopes.len() {
            self.scope_ids.push(0);
        } else {
            self.scope_ids[self.scopes.len() - 1] += 1;
        }
        Ok(())
    }

    fn pop_scope(&mut self) -> ResolverResult {
        if let Some((name, located)) = self.scopes.pop().and_then(|scope| {
            scope
                .into_iter()
                .find(|(_, state)| state.item != VarState::Used)
        }) {
            Err(Error::UnusedDeclaration(name.clone()).at(&located))
        } else {
            Ok(())
        }
    }

    fn function(
        &mut self,
        parameters: &Vec<Located<String>>,
        body: &Located<Statement>,
        function_type: FunctionType,
        location: &impl Locateable,
    ) -> ResolverResult {
        let enclosing_type = std::mem::replace(&mut self.function_type, function_type);
        self.push_scope()?;
        for parameter in parameters.iter() {
            self.set_value(parameter.item.clone(), VarState::Defined.at(location));
        }
        self.statement(body)?;
        self.pop_scope()?;
        self.function_type = enclosing_type;
        Ok(())
    }

    fn resolve_local(&mut self, name: &String, location: Location) -> ResolverResult {
        for (i, scope) in self.scopes.iter_mut().enumerate().rev() {
            if scope.contains_key(name) {
                scope.insert(name.clone(), VarState::Used.at(&location));
                let ref_id = ReferenceId {
                    identifier: name.clone(),
                    path: self.scope_ids[..i].to_vec(),
                };
                self.interpreter.resolve(location, ref_id);
                return Ok(());
            }
        }
        Err(Error::UndefinedVariable(name.clone()).at(&location))
    }
}
