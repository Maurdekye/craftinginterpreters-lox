use std::{
    borrow::{Borrow, Cow},
    collections::hash_map::Entry,
    fmt::Display,
    rc::Rc,
    time::SystemTime,
};

use polonius_the_crab::{exit_polonius, polonius, polonius_return, polonius_try};
use replace_with::replace_with_or_abort;

use crate::{
    lexer::Token,
    parser::{Expression, Statement},
    util::{
        AppendLocatedError, AppendLocatedErrorWithSignal, AsOwned, EntryInsert, Locateable,
        Located, LocatedAt, Signaling, SignalingResult,
    },
};

use thiserror::Error as ThisError;

use self::environment::{Environment, ScopeHandle};

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    // dont forget to update stack_contains when adding new scoped errors
    #[error("In this assignment:\n{0}")]
    AssignmentEvaluation(Box<Located<Error>>),
    #[error("At this unary operator:\n{0}")]
    UnaryEvaluation(Box<Located<Error>>),
    #[error("In this binary expression:\n{0}")]
    BinaryEvaluation(Box<Located<Error>>),
    #[error("In this ternary:\n{0}")]
    TernaryEvaluation(Box<Located<Error>>),
    #[error("Trying to read this variable:\n{0}")]
    VariableResolution(Box<Error>),

    #[error("In this var statement:\n{0}")]
    VarEvaluation(Box<Located<Error>>),
    #[error("In this while statement:\n{0}")]
    WhileEvaluation(Box<Located<Error>>),
    #[error("In this if statement:\n{0}")]
    IfEvaluation(Box<Located<Error>>),
    #[error("In this print statement:\n{0}")]
    PrintEvaluation(Box<Located<Error>>),
    #[error("In this block:\n{0}")]
    BlockEvaluation(Box<Located<Error>>),
    #[error("In this statement:\n{0}")]
    ExpressionStatementEvaluation(Box<Located<Error>>),
    #[error("In this call:\n{0}")]
    FunctionCall(Box<Located<Error>>), // eventually i hope to include the called function name in here

    #[error("Can only call functions and class constructors, not '{0}'")]
    InvalidCallable(Value),
    #[error("This function takes {0} arguments, but you passed {1}")]
    IncorrectArity(usize, usize),
    #[error("This is supposed to be true or false, but it was '{0}'")]
    InvalidIfCondition(Value),
    #[error("You haven't defined '{0}' yet")]
    UndeclaredVariable(String),
    #[error("'{0}' isn't initialized")]
    UninitializedVariable(String),
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

    #[error("Can't 'break' when not in a loop")]
    InvalidBreak,
    #[error("Can't 'continue' when not in a loop")]
    InvalidContinue,
    #[error("Can't 'return' outside of a function")]
    InvalidReturn,
}

#[derive(Clone, Debug)]
pub enum Signal {
    Break,
    Continue,
    Return(Option<Value>),
}

#[derive(Clone, Debug)]
pub enum MaybeWithSignal<T> {
    NoSignal(T),
    WithSignal(T, Signal),
}

impl<T> MaybeWithSignal<T> {
    pub fn map<V>(self, f: impl FnOnce(T) -> V) -> MaybeWithSignal<V> {
        match self {
            MaybeWithSignal::NoSignal(inner) => MaybeWithSignal::NoSignal(f(inner)),
            MaybeWithSignal::WithSignal(inner, signal) => {
                MaybeWithSignal::WithSignal(f(inner), signal)
            }
        }
    }

    pub fn into_inner(self) -> T {
        let (MaybeWithSignal::NoSignal(inner) | MaybeWithSignal::WithSignal(inner, _)) = self;
        inner
    }
}

#[derive(Clone, Debug)]
pub enum FunctionImplementation {
    Lox(Rc<Vec<Located<String>>>, Rc<Located<Statement>>),
    Clock,
}

#[derive(Clone, Debug)]
pub struct Function {
    arity: usize,
    scope: Rc<ScopeHandle>, // really don't like this...
    implementation: FunctionImplementation,
}

impl Function {
    pub fn call(
        &mut self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> ExpressionEvalResult {
        match &self.implementation {
            FunctionImplementation::Lox(parameters, body) => {
                // substitute interpreter's scope with function's scope during execution
                let function_scope = interpreter.environment.dupe(&self.scope).unwrap();
                let prior_scope = std::mem::replace(&mut interpreter.scope_handle, function_scope);

                // new scope for function body
                replace_with_or_abort(&mut interpreter.scope_handle, |handle| {
                    interpreter.environment.push(handle)
                });

                // register parameters as variables in the function body
                for (name, value) in parameters.iter().map(|s| s.item.clone()).zip(args) {
                    interpreter
                        .environment
                        .top_entry(&interpreter.scope_handle, name)
                        .insert(value);
                }

                // eval function and expect a return value
                let return_val = match interpreter.statement(body) {
                    Err(MaybeWithSignal::WithSignal(_, Signal::Return(Some(value)))) => Ok(value),
                    Err(MaybeWithSignal::WithSignal(_, Signal::Return(None))) | Ok(_) => {
                        Ok(Value::Nil)
                    }
                    Err::<(), _>(err) => Err::<Value, _>(err),
                };

                // pop function body's scope
                replace_with_or_abort(&mut interpreter.scope_handle, |handle| {
                    interpreter
                        .environment
                        .pop(handle)
                        .expect("Will always have just pushed a scope")
                });

                // return interpreter's scope back to prior state
                let function_scope = std::mem::replace(&mut interpreter.scope_handle, prior_scope);
                interpreter.environment.drop(function_scope);

                // return result
                return_val
            }
            FunctionImplementation::Clock => Ok(Value::Number(
                SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .expect("Unix epoch is always in the past")
                    .as_secs_f64(),
            )),
        }
    }
}

impl Display for FunctionImplementation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match match self {
            Self::Lox(_, body) => Ok(format!("fn @ {}", body.location())),
            Self::Clock => Err("clock"),
        } {
            Ok(s) => write!(f, "{s}"),
            Err(s) => write!(f, "native fn {s}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Class;

#[derive(Clone, Debug)]
pub enum Callable {
    Function(Function),
    Class(Class),
}

impl Callable {
    pub fn call(
        &mut self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> ExpressionEvalResult {
        match self {
            Callable::Function(function) => function.call(interpreter, args),
            Callable::Class(_class) => todo!(),
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Callable::Function(function) => function.arity,
            Callable::Class(_class) => todo!(),
        }
    }
}

impl TryFrom<Value> for Callable {
    type Error = Value;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Function(function) => Ok(Callable::Function(function)),
            Value::Class(class) => Ok(Callable::Class(class)),
            other => Err(other),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Function(Function),
    Class(Class),
    String(String),
    Number(f64),
    True,
    False,
    Nil,
    Uninitialized,
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Function(_), Self::Function(_)) => false,
            (Self::Class(_), Self::Class(_)) => false,
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::Number(l0), Self::Number(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
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

impl Into<bool> for &Value {
    fn into(self) -> bool {
        match self {
            Value::False | Value::Nil => false,
            _ => true,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Function(fun) => write!(f, "<{}>", fun.implementation),
            Value::Class(_c) => todo!("implement classes first"),
            Value::String(s) => write!(f, "\"{s}\""),
            Value::Number(n) => write!(f, "{n}"),
            Value::True => write!(f, "true"),
            Value::False => write!(f, "false"),
            Value::Nil => write!(f, "nil"),
            Value::Uninitialized => write!(f, "uninitialized"),
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

// #[derive(Debug)]
// pub enum Environment {
//     Global(HashMap<String, Value>),
//     Scope(HashMap<String, Value>, Box<Environment>),
// }

// impl Environment {
//     pub fn new() -> Self {
//         Self::Global(HashMap::new())
//     }

//     pub fn entry<'a>(&'a mut self, key: String) -> Entry<'a, String, Value> {
//         let (mut env, outer_scope) = match self {
//             Environment::Global(env) => return env.entry(key),
//             Environment::Scope(env, outer_scope) => (env, outer_scope),
//         };
//         let key = polonius!(|env| -> Entry<'polonius, String, Value> {
//             match env.entry(key) {
//                 entry @ Entry::Occupied(_) => polonius_return!(entry),
//                 Entry::Vacant(vacant) => exit_polonius!(vacant.into_key()),
//             }
//         });
//         let key = match outer_scope.entry(key) {
//             entry @ Entry::Occupied(_) => return entry,
//             Entry::Vacant(vacant) => vacant.into_key(),
//         };
//         return env.entry(key);
//     }

//     pub fn top_entry(&mut self, key: String) -> Entry<'_, String, Value> {
//         let (Environment::Global(env) | Environment::Scope(env, _)) = self;
//         env.entry(key)
//     }

//     pub fn push(&mut self) {
//         replace_with_or_abort(self, |old_self| {
//             Environment::Scope(HashMap::new(), Box::new(old_self))
//         })
//     }

//     pub fn pop(&mut self) -> Result<(), AtGlobalScopeError> {
//         let mut result = Ok(());
//         replace_with_or_abort(self, |old_self| match old_self {
//             Environment::Global(_) => {
//                 result = Err(AtGlobalScopeError);
//                 old_self
//             }
//             Environment::Scope(_, outer_scope) => *outer_scope,
//         });
//         result
//     }
// }

mod environment {
    use std::collections::{hash_map::Entry, HashMap};

    use polonius_the_crab::{exit_polonius, polonius, polonius_return};
    use thiserror::Error as ThisError;

    use super::Value;

    #[derive(Debug, ThisError)]
    pub enum Error {
        #[error("Scope handle not associated with a scope")]
        NoScope,
        #[error("Scope associated with handle does not have a parent")]
        NoParentScope,
    }

    #[derive(Debug)]
    pub struct ScopeHandle(usize);

    #[derive(Debug)]
    pub struct Scope {
        references: usize,
        env: HashMap<String, Value>,
        parent: Option<ScopeHandle>,
    }

    #[derive(Debug)]
    pub struct Environment {
        scopes: Vec<Option<Scope>>,
    }

    impl Environment {
        pub fn new() -> (Environment, ScopeHandle) {
            let this = Environment {
                scopes: vec![Some(Scope {
                    references: 1,
                    env: HashMap::new(),
                    parent: None,
                })],
            };
            (this, ScopeHandle(0))
        }

        fn next_vacant_handle(&mut self) -> ScopeHandle {
            if let Some(id) = self.scopes.iter().position(|x| x.is_none()) {
                ScopeHandle(id)
            } else {
                self.scopes.push(None);
                ScopeHandle(self.scopes.len() - 1)
            }
        }

        fn place_scope(&mut self, scope: Scope) -> ScopeHandle {
            let handle = self.next_vacant_handle();
            self.scopes[handle.0] = Some(scope);
            handle
        }

        fn retrieve_scope(&mut self, handle: &ScopeHandle) -> Option<&mut Scope> {
            self.scopes.get_mut(handle.0).map(Option::as_mut).flatten()
        }

        pub fn dupe(&mut self, handle: &ScopeHandle) -> Result<ScopeHandle, Error> {
            let Some(scope) = self.retrieve_scope(handle) else {
                return Err(Error::NoScope);
            };
            scope.references += 1;
            Ok(ScopeHandle(handle.0))
        }

        pub fn drop(&mut self, handle: ScopeHandle) {
            (|| -> Option<()> {
                let scope = self.retrieve_scope(&handle)?;
                scope.references -= 1;
                if scope.references == 0 {
                    let inner_scope = std::mem::take(self.scopes.get_mut(handle.0)?)?;
                    if handle.0 == self.scopes.len() - 1 {
                        self.scopes.pop();
                    }
                    let parent = inner_scope.parent?;
                    self.drop(parent);
                }
                Some(())
            })();
        }

        pub fn push(&mut self, handle: ScopeHandle) -> ScopeHandle {
            let new_scope = Scope {
                references: 1,
                env: HashMap::new(),
                parent: Some(handle),
            };
            self.place_scope(new_scope)
        }

        pub fn pop(&mut self, handle: ScopeHandle) -> Result<ScopeHandle, (ScopeHandle, Error)> {
            let Some(scope) = self.retrieve_scope(&handle) else {
                return Err((handle, Error::NoScope));
            };
            let Some(parent_handle) = std::mem::take(&mut scope.parent) else {
                return Err((handle, Error::NoParentScope));
            };
            self.drop(handle);
            Ok(parent_handle)
        }

        pub fn entry_checked<'a>(
            &'a mut self,
            handle: &ScopeHandle,
            key: String,
        ) -> Result<Entry<'a, String, Value>, String> {
            let mut this = self;
            let (key, parent_handle) =
                polonius!(|this| -> Result<Entry<'polonius, String, Value>, String> {
                    let Some(scope) = this.retrieve_scope(&handle) else {
                        polonius_return!(Err(key));
                    };
                    let parent_handle = match &scope.parent {
                        None => polonius_return!(Ok(scope.env.entry(key))),
                        Some(parent_handle) => ScopeHandle(parent_handle.0),
                    };
                    match scope.env.entry(key) {
                        entry @ Entry::Occupied(_) => polonius_return!(Ok(entry)),
                        Entry::Vacant(vacant) => exit_polonius!((vacant.into_key(), parent_handle)),
                    }
                });
            let key = polonius!(|this| -> Result<Entry<'polonius, String, Value>, String> {
                match this.entry_checked(&parent_handle, key) {
                    Ok(entry @ Entry::Occupied(_)) => polonius_return!(Ok(entry)),
                    Ok(Entry::Vacant(vacant)) => exit_polonius!(vacant.into_key()),
                    Err(key) => exit_polonius!(key),
                }
            });
            // this is redundant... but polonius is too annoying to work around to try and remove this
            let Some(scope) = this.retrieve_scope(&handle) else {
                return Err(key);
            };
            Ok(scope.env.entry(key))
        }

        pub fn entry<'a>(
            &'a mut self,
            handle: &ScopeHandle,
            key: String,
        ) -> Entry<'a, String, Value> {
            self.entry_checked(handle, key).unwrap()
        }

        pub fn top_entry_checked<'a>(
            &'a mut self,
            handle: &ScopeHandle,
            key: String,
        ) -> Result<Entry<'a, String, Value>, String> {
            let Some(scope) = self.retrieve_scope(&handle) else {
                return Err(key);
            };
            Ok(scope.env.entry(key))
        }

        pub fn top_entry<'a>(
            &'a mut self,
            handle: &ScopeHandle,
            key: String,
        ) -> Entry<'a, String, Value> {
            self.top_entry_checked(handle, key).unwrap()
        }
    }
}

#[derive(Clone, Debug, ThisError)]
#[error("Already at global scope")]
pub struct AtGlobalScopeError;

type EvalError = MaybeWithSignal<Located<Error>>;
type StatementEvalResult = Result<(), EvalError>;
type ExpressionEvalResult = Result<Value, EvalError>;
type ExpressionEvalResultCow<'a> = Result<Cow<'a, Value>, EvalError>;

pub struct Interpreter {
    environment: Environment,
    scope_handle: ScopeHandle,
}

impl Interpreter {
    pub fn new() -> Self {
        let (environment, scope_handle) = Environment::new();
        let mut this = Self {
            environment,
            scope_handle,
        };
        let handle = this.environment.dupe(&this.scope_handle).unwrap();
        this.environment
            .entry(&this.scope_handle, "clock".into())
            .or_insert(Value::Function(Function {
                arity: 0,
                scope: Rc::new(handle),
                implementation: FunctionImplementation::Clock,
            })); // insert clock native function into global scope
        this
    }

    pub fn interpret(
        &mut self,
        statements: &Vec<Located<Statement>>,
    ) -> Result<(), Located<Error>> {
        for statement in statements {
            self.statement(statement)
                .map_err(MaybeWithSignal::into_inner)?;
        }
        Ok(())
    }

    fn statement(&mut self, statement: &Located<Statement>) -> StatementEvalResult {
        let location = &statement.location();
        match &statement.item {
            Statement::Break => {
                return Err(Error::InvalidBreak.at(location).signaling(Signal::Break))
            }
            Statement::Continue => {
                return Err(Error::InvalidContinue
                    .at(location)
                    .signaling(Signal::Continue))
            }
            Statement::Return(value) => {
                let return_value = value
                    .as_ref()
                    .map(|value| self.evaluate(value))
                    .transpose()
                    .map(|ok| ok.map(Cow::into_owned))?; // return value of function must be owned
                return Err(Error::InvalidReturn
                    .at(location)
                    .signaling(Signal::Return(return_value)));
            }
            Statement::If(condition, true_branch, false_branch) => {
                self.if_statement(condition, true_branch.as_ref(), false_branch.as_ref())
                    .with_maybe_signaled_err_at(Error::IfEvaluation, location)?;
            }
            Statement::While(condition, body) => {
                self.while_statement(condition, body.as_ref())
                    .with_maybe_signaled_err_at(Error::WhileEvaluation, location)?;
            }
            Statement::Print(expression) => {
                let result = self
                    .evaluate(expression)
                    .with_maybe_signaled_err_at(Error::PrintEvaluation, location)?;
                let repr: Cow<'_, String> = match result.borrow() {
                    Value::String(s) => Cow::Borrowed(s),
                    value => Cow::Owned(format!("{value}")),
                };
                println!("{repr}");
            }
            Statement::Expression(expression) => {
                self.evaluate(expression)
                    .with_maybe_signaled_err_at(Error::ExpressionStatementEvaluation, location)?;
            }
            Statement::Var(name, maybe_initializer) => {
                let value = match maybe_initializer {
                    Some(expression) => self
                        .evaluate(expression)
                        .with_maybe_signaled_err_at(Error::VarEvaluation, location)?
                        .into_owned(), // own must occur in order to store the value
                    None => Value::Uninitialized,
                };
                self.environment
                    .top_entry(&self.scope_handle, name.to_owned())
                    .insert(value);
            }
            Statement::Block(statements) => {
                replace_with_or_abort(&mut self.scope_handle, |handle| {
                    self.environment.push(handle)
                });
                let result = self
                    .block(statements)
                    .with_maybe_signaled_err_at(Error::BlockEvaluation, location);
                replace_with_or_abort(&mut self.scope_handle, |handle| {
                    self.environment
                        .pop(handle)
                        .expect("Will always have just pushed a scope")
                });
                result?;
            }
            Statement::Function(name, parameters, body) => {
                let function = self.function_declaration(parameters.clone(), body.clone())?;
                self.environment
                    .entry(&self.scope_handle, name.item.clone())
                    .insert(function)
            }
        }
        Ok(())
    }

    fn if_statement(
        &mut self,
        condition: &Located<Expression>,
        true_branch: &Located<Statement>,
        false_branch: &Option<Located<Statement>>,
    ) -> StatementEvalResult {
        if {
            let condition_value = self.evaluate(condition)?;
            let condition_value: &Value = condition_value.borrow();
            condition_value.into()
        } {
            self.statement(true_branch)?;
        } else if let Some(false_branch) = false_branch {
            self.statement(false_branch)?;
        }
        Ok(())
    }

    fn while_statement(
        &mut self,
        condition: &Located<Expression>,
        body: &Located<Statement>,
    ) -> StatementEvalResult {
        while {
            let condition_value = self.evaluate(condition)?;
            let condition_value: &Value = condition_value.borrow();
            condition_value.into()
        } {
            match self.statement(body) {
                Err(MaybeWithSignal::WithSignal(_, Signal::Break)) => break,
                Err(MaybeWithSignal::WithSignal(_, Signal::Continue)) => continue,
                other => other?,
            }
        }
        Ok(())
    }

    fn block(&mut self, statements: &Vec<Located<Statement>>) -> StatementEvalResult {
        for statement in statements {
            self.statement(statement)?;
        }
        Ok(())
    }

    pub fn evaluate(&mut self, expression: &Located<Expression>) -> ExpressionEvalResultCow<'_> {
        let location = &expression.location();
        match &expression.item {
            Expression::Literal(literal_token) => self
                .literal(literal_token)
                .as_owned()
                .with_err_at(Error::InvalidLiteral, location)
                .map_err(MaybeWithSignal::NoSignal),
            Expression::Variable(name) => self
                .variable(name.to_owned())
                .with_err_at(Error::VariableResolution, location)
                .map_err(MaybeWithSignal::NoSignal),
            Expression::Assignment(name, sub_expression) => self
                .assignment(name.clone(), sub_expression) // clone is necessary, because variable reassignment may occur
                .with_maybe_signaled_err_at(Error::AssignmentEvaluation, location),
            Expression::Grouping(sub_expression) => self.evaluate(sub_expression),
            Expression::Unary(unary_operator, unary_expr) => self
                .unary(unary_operator, unary_expr)
                .as_owned()
                .with_maybe_signaled_err_at(Error::UnaryEvaluation, location),
            Expression::Binary(binary_operator, lhs_expr, rhs_expr) => self
                .binary(binary_operator, lhs_expr, rhs_expr)
                .with_maybe_signaled_err_at(Error::BinaryEvaluation, location),
            Expression::Ternary(condition_expr, true_branch_expr, false_branch_expr) => self
                .ternary(condition_expr, true_branch_expr, false_branch_expr)
                .with_maybe_signaled_err_at(Error::TernaryEvaluation, location),
            Expression::Call(function, arguments) => self
                .call(function.as_ref(), &arguments[..])
                .as_owned()
                .with_maybe_signaled_err_at(Error::FunctionCall, location),
            Expression::Lambda(parameters, body) => self
                .function_declaration(parameters.clone(), body.clone())
                .as_owned(),
        }
    }

    fn function_declaration(
        &mut self,
        parameters: Rc<Vec<Located<String>>>,
        body: Rc<Located<Statement>>,
    ) -> ExpressionEvalResult {
        let new_handle = self.environment.dupe(&self.scope_handle).unwrap();
        Ok(Value::Function(Function {
            arity: parameters.len(),
            scope: Rc::new(new_handle),
            implementation: FunctionImplementation::Lox(parameters, body), // rc clones, cheap
        }))
    }

    fn literal(&mut self, literal: &Located<Token>) -> Result<Value, Token> {
        literal.item.clone().try_into() // must clone the literal to resolve its value
    }

    fn variable(&mut self, name: String) -> Result<Cow<Value>, Error> {
        match self.environment.entry(&self.scope_handle, name) {
            Entry::Occupied(occupied) => match occupied.get() {
                Value::Uninitialized => Err(Error::UninitializedVariable(occupied.key().clone())), // error contents must be owned (no `OccupiedEntry::into_key` 🙁)
                _ => Ok(Cow::Borrowed(occupied.into_mut())),
            },
            Entry::Vacant(vacant) => Err(Error::UndeclaredVariable(vacant.into_key())),
        }
    }

    fn assignment<'a>(
        &'a mut self,
        name: Located<String>,
        expression: &Located<Expression>,
    ) -> ExpressionEvalResultCow<'a> {
        let (name, location) = name.split();
        let value = self.evaluate(expression)?.into_owned(); // own must occur in order to store the value
        match self.environment.entry(&self.scope_handle, name) {
            Entry::Vacant(vacant) => Err(Error::UndeclaredVariable(vacant.into_key())
                .at(&location)
                .no_signal()),
            Entry::Occupied(mut entry) => {
                entry.insert(value);
                Ok(Cow::Borrowed(entry.into_mut())) // everything is cows so that i can write this line here :>
            }
        }
    }

    fn unary(
        &mut self,
        unary: &Located<Token>,
        unary_expr: &Located<Expression>,
    ) -> ExpressionEvalResult {
        let location = unary.location();
        let value = self.evaluate(unary_expr)?;
        match (&unary.item, value.borrow()) {
            (Token::Minus, Value::Number(value)) => Ok(Value::Number(-value)),
            (Token::Bang, operand) => {
                let bool_value: bool = operand.into();
                Ok((!bool_value).into())
            }
            (unary, _) => Err(Error::InvalidUnary(unary.clone(), value.into_owned())
                .at(&location)
                .no_signal()), // error contents must be owned
        }
    }

    fn call(
        &mut self,
        function: &Located<Expression>,
        arguments: &[Located<Expression>],
    ) -> ExpressionEvalResult {
        let location = function.location();
        let function = self.evaluate(function)?.into_owned(); // must own function before calling it

        // check if callable
        let mut function: Callable = function
            .try_into()
            .with_err_at(Error::InvalidCallable, &location)
            .err_no_signal()?;

        // check arity
        if arguments.len() != function.arity() {
            return Err(Error::IncorrectArity(function.arity(), arguments.len())
                .at(&location)
                .no_signal());
        }

        // collect arguments
        let mut argument_values = Vec::new();
        for arg in arguments {
            argument_values.push(self.evaluate(arg)?.into_owned()); // must own all function arguments before calling function
        }

        // call function
        function.call(self, argument_values)
    }

    fn binary(
        &mut self,
        binary: &Located<Token>,
        lhs_expr: &Located<Expression>,
        rhs_expr: &Located<Expression>,
    ) -> ExpressionEvalResultCow<'_> {
        let binary_location = binary.location();
        let lhs_location = lhs_expr.location();

        let mut this = self; // cannot use polonius_the_crab on `self`

        let (lhs_truthiness, lhs_value) = polonius!(|this| -> ExpressionEvalResultCow<'polonius> {
            let lhs_value = polonius_try!(this.evaluate(lhs_expr));

            // match short circuit boolean operations before evaluating right hand side
            let lhs_borrow: &Value = lhs_value.borrow();
            match (lhs_borrow.into(), &binary.item) {
                (false, Token::And) | (true, Token::Or) => {
                    polonius_return!(Ok(lhs_value));
                }
                (lhs_truthiness, _) => exit_polonius!((lhs_truthiness, lhs_value.into_owned())), // this own may not be cheap, but it is unavoidable, because we must also borrow rhs 😔
            };
        });

        let rhs_value = this.evaluate(rhs_expr)?;

        // finish short circuit boolean evaluation
        match (lhs_truthiness, &binary.item) {
            (true, Token::And) | (false, Token::Or) => {
                return Ok(rhs_value);
            }
            _ => (),
        }

        match (lhs_value.borrow(), &binary.item, rhs_value.borrow()) {
            // equality
            (lhs, Token::EqualEqual, rhs) => Ok(Cow::Owned((lhs == rhs).into())),
            (lhs, Token::BangEqual, rhs) => Ok(Cow::Owned((lhs != rhs).into())),

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
                Err(Error::DivisionByZero(lhs_value)
                    .at(&lhs_location)
                    .no_signal())
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
                    Error::InvalidBinary(lhs_value, operator.clone(), rhs_value.into_owned())
                        .at(&binary_location)
                        .no_signal(),
                ) // error contents must be owned
            }
        }
    }

    fn ternary(
        &mut self,
        condition_expr: &Located<Expression>,
        true_branch_expr: &Located<Expression>,
        false_branch_expr: &Located<Expression>,
    ) -> ExpressionEvalResultCow<'_> {
        let condition_value = self.evaluate(condition_expr)?;
        let condition_bool: &Value = condition_value.borrow();
        if condition_bool.into() {
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
        let (mut env, mut handle) = Environment::new();
        env.entry(&handle, "x".to_string())
            .or_insert(Value::Number(5.0));
        env.entry(&handle, "y".to_string())
            .or_insert(Value::Number(10.0));
        handle = env.push(handle);
        env.entry(&handle, "x".to_string())
            .and_modify(|x| *x = Value::Number(40.0));
        env.entry(&handle, "z".to_string())
            .or_insert(Value::Number(607.0));
        dbg!(&env);
        env.top_entry(&handle, "x".to_string())
            .or_insert(Value::Number(900.0));
        dbg!(&env);
        handle = env.pop(handle).unwrap();
        env.entry(&handle, "x".to_string())
            .and_modify(|x| *x = Value::Number(18.0));
        dbg!(&env);
    }
}
