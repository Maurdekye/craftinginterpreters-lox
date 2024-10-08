use std::{
    borrow::Borrow, cell::RefCell, collections::HashMap, fmt::Display, rc::Rc, time::SystemTime,
};

use crate::{
    lexer::Token,
    parser::{Expression, Statement},
    util::{
        AppendLocatedError, AppendLocatedErrorWithSignal, Locateable, Located, LocatedAt, Location,
        Signaling, SignalingResult,
    },
};

use thiserror::Error as ThisError;

use self::environment::{AsThunk, Environment, ValueThunk};

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
    #[error("Only instances have fields")]
    GetOnNonObject,
    #[error("Only instances have fields set")]
    SetOnNonObject,
    #[error("Instance doesn't have field '{0}'")]
    InvalidFieldAccess(String),
    #[error("'{0}' is not a class")]
    InvalidSuperclass(String),

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
    DeepCopy,
}

#[derive(Clone, Debug)]
pub struct Function {
    arity: usize,
    environment: Environment,
    is_initializer: bool,
    is_getter: bool,
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
                let prior_scope =
                    std::mem::replace(&mut interpreter.environment, self.environment.clone());

                // new scope for function body
                interpreter.environment.push();

                // register parameters as variables in the function body
                for (name, value) in parameters.iter().map(|s| s.item.clone()).zip(args) {
                    interpreter.environment.declare(name, value);
                }

                // eval function and expect a return value
                let mut return_val = match interpreter.statement(body) {
                    Err(MaybeWithSignal::WithSignal(_, Signal::Return(Some(value)))) => Ok(value),
                    Err(MaybeWithSignal::WithSignal(_, Signal::Return(None))) | Ok(_) => {
                        Ok(Value::Nil)
                    }
                    Err::<(), _>(err) => Err::<Value, _>(err),
                };

                // return this instead of the normal return value if running an initializer
                if self.is_initializer {
                    return_val = Ok(interpreter
                        .environment
                        .get(String::from("this"))
                        .expect("Initializer will always have a 'this' variable declared"));
                }

                // pop function body's scope
                interpreter
                    .environment
                    .pop()
                    .expect("Will always have just pushed a scope");

                // return interpreter's scope back to prior state
                interpreter.environment = prior_scope;

                // return result
                return_val
            }
            FunctionImplementation::Clock => Ok(Value::Number(
                SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .expect("Unix epoch is always in the past")
                    .as_secs_f64(),
            )),
            FunctionImplementation::DeepCopy => Ok(match &args[0] {
                Value::Instance(instance) => {
                    let inner_cell = RefCell::borrow(&instance);
                    Value::Instance(Rc::new(RefCell::new(inner_cell.clone())))
                }
                value => value.clone(),
            }),
        }
    }
}

impl Display for FunctionImplementation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match match self {
            Self::Lox(_, body) => Ok(format!("fn @ {}", body.location())),
            Self::Clock => Err("clock"),
            Self::DeepCopy => Err("deepcopy"),
        } {
            Ok(s) => write!(f, "{s}"),
            Err(s) => write!(f, "native fn {s}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Class {
    name: String,
    superclass: Option<Rc<Class>>,
    methods: HashMap<String, Value>,
    class_methods: HashMap<String, Value>,
}

impl Class {
    pub fn find_method(&self, name: &String) -> Option<Value> {
        if let Some(method) = self.methods.get(name) {
            return Some(method.clone());
        }

        if let Some(superclass) = &self.superclass {
            if let Some(method) = superclass.find_method(name) {
                return Some(method);
            }
        }

        None
    }
}

#[derive(Clone, Debug)]
pub enum Callable {
    Function(Function),
    Class(Rc<Class>),
}

impl Callable {
    pub fn call(
        &mut self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> ExpressionEvalResult {
        match self {
            Callable::Function(function) => function.call(interpreter, args),
            Callable::Class(class) => {
                let instance = Rc::new(RefCell::new(Instance {
                    class: class.clone(),
                    fields: HashMap::new(),
                }));
                if let Some(Value::Function(init)) = &mut class.methods.get("init").cloned() {
                    instance.bind(init);
                    init.call(interpreter, args)?;
                }
                Ok(Value::Instance(instance))
            }
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Callable::Function(function) => function.arity,
            Callable::Class(class) => {
                if let Some(Value::Function(init)) = class.methods.get("init") {
                    init.arity
                } else {
                    0
                }
            }
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
pub struct Instance {
    class: Rc<Class>,
    fields: HashMap<String, Value>,
}

pub trait RcRefCellInstance {
    fn get(&self, interpreter: &mut Interpreter, field: &Located<String>) -> ExpressionEvalResult;
    fn bind(&self, method: &mut Function);
}

impl RcRefCellInstance for Rc<RefCell<Instance>> {
    fn get(&self, interpreter: &mut Interpreter, field: &Located<String>) -> ExpressionEvalResult {
        if let Some(value) = RefCell::borrow(self).fields.get(&field.item).cloned() {
            return Ok(value);
        }

        if let Some(mut method) = RefCell::borrow(self).class.find_method(&field.item) {
            if let Value::Function(method) = &mut method {
                self.bind(method);
                if method.is_getter {
                    let getter_result = method.call(interpreter, Vec::new())?;
                    return Ok(getter_result);
                }
            }

            return Ok(method);
        }

        Err(Error::InvalidFieldAccess(field.item.clone())
            .at(&field.location())
            .no_signal())
    }

    fn bind(&self, method: &mut Function) {
        method.environment.push();
        method
            .environment
            .declare(String::from("this"), Value::Instance(self.clone()));
    }
}

impl Instance {
    pub fn set(&mut self, field: &Located<String>, value: Value) -> StatementEvalResult {
        self.fields.insert(field.item.clone(), value);
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Function(Function),
    Class(Rc<Class>),
    String(String),
    Number(f64),
    Instance(Rc<RefCell<Instance>>),
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
            Value::Function(function) => write!(f, "<{}>", function.implementation),
            Value::Class(class) => write!(f, "{}", class.name),
            Value::String(string) => write!(f, "\"{string}\""),
            Value::Number(number) => write!(f, "{number}"),
            Value::Instance(instance) => {
                write!(f, "{} instance", RefCell::borrow(instance).class.name)
            }
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

impl Default for Value {
    fn default() -> Self {
        Value::Nil
    }
}

mod environment {
    use std::{
        cell::RefCell,
        collections::{hash_map::Entry, HashMap},
        rc::Rc,
    };

    use replace_with::replace_with_or_abort;
    use thiserror::Error as ThisError;

    use super::Value;

    pub enum ValueThunk {
        Thunk {
            scope: Rc<RefCell<Scope>>,
            ident: String,
        },
        Value(Value),
    }

    impl ValueThunk {
        pub fn into_owned(self) -> Value {
            match self {
                ValueThunk::Thunk { scope, ident } => {
                    scope.borrow().env.get(&ident).cloned().unwrap_or_default()
                }
                ValueThunk::Value(value) => value,
            }
        }

        // not possible :(
        // pub fn get(&self) -> &Value {
        //     match self {
        //         ValueThunk::Thunk { scope, ident } => {
        //             scope.borrow().env.get(ident).unwrap_or(&Value::Nil)
        //         }
        //         ValueThunk::Value(value) => &value,
        //     }
        // }
    }

    pub trait AsThunk {
        type Output;

        fn as_thunk(self) -> Self::Output;
    }

    impl<E> AsThunk for Result<Value, E> {
        type Output = Result<ValueThunk, E>;

        fn as_thunk(self) -> Self::Output {
            self.map(ValueThunk::Value)
        }
    }

    #[derive(Debug)]
    pub struct Scope {
        env: HashMap<String, Value>,
        parent: Option<Rc<RefCell<Scope>>>,
    }

    impl Scope {
        fn new() -> Self {
            Self {
                env: HashMap::new(),
                parent: None,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct Environment(Rc<RefCell<Scope>>);

    impl Environment {
        pub fn new() -> Self {
            Environment(Rc::new(RefCell::new(Scope::new())))
        }

        pub fn list_idents(&self) -> Vec<String> {
            self.0.borrow().env.keys().cloned().collect()
        }

        pub fn push(&mut self) {
            replace_with_or_abort(&mut self.0, |scope| {
                let new_scope = Scope {
                    env: HashMap::new(),
                    parent: Some(scope),
                };
                Rc::new(RefCell::new(new_scope))
            })
        }

        pub fn pop(&mut self) -> Result<(), AtGlobalScopeError> {
            let Some(parent) = std::mem::take(&mut self.0.borrow_mut().parent) else {
                return Err(AtGlobalScopeError);
            };
            replace_with_or_abort(&mut self.0, |_| parent);
            Ok(())
        }

        pub fn get(&mut self, mut key: String) -> Result<Value, String> {
            let mut scope = self.0.clone();
            loop {
                key = match scope.borrow_mut().env.entry(key) {
                    Entry::Occupied(entry) => return Ok(entry.get().clone()),
                    Entry::Vacant(vacant) => vacant.into_key(),
                };
                let parent = match &scope.borrow_mut().parent {
                    None => return Err(key),
                    Some(parent) => parent.clone(),
                };
                scope = parent;
            }
        }

        fn ancestor(&mut self, depth: usize) -> Option<Rc<RefCell<Scope>>> {
            let mut scope = self.0.clone();
            for _ in 0..depth {
                let parent = match &scope.borrow_mut().parent {
                    None => return None,
                    Some(parent) => parent.clone(),
                };
                scope = parent;
            }
            Some(scope)
        }

        pub fn get_at(&mut self, key: String, depth: usize) -> Result<Value, String> {
            let Some(scope) = self.ancestor(depth) else {
                return Err(key);
            };
            let result = match scope.borrow_mut().env.entry(key) {
                Entry::Occupied(entry) => Ok(entry.get().clone()),
                Entry::Vacant(vacant) => Err(vacant.into_key()),
            };
            result
        }

        pub fn declare(&mut self, key: String, value: Value) {
            let mut scope = self.0.borrow_mut();
            scope.env.insert(key, value);
        }

        pub fn assign(&mut self, mut key: String, value: Value) -> Result<ValueThunk, String> {
            let mut scope = self.0.clone();
            loop {
                key = match scope.borrow_mut().env.entry(key.clone()) {
                    Entry::Occupied(mut entry) => {
                        entry.insert(value);
                        return Ok(ValueThunk::Thunk {
                            scope: scope.clone(),
                            ident: key,
                        }); // new ver. of optimization (may actually be slower)
                    }
                    Entry::Vacant(vacant) => vacant.into_key(),
                };
                let parent = match &scope.borrow_mut().parent {
                    None => return Err(key),
                    Some(parent) => parent.clone(),
                };
                scope = parent;
            }
        }

        pub fn assign_at(
            &mut self,
            key: String,
            value: Value,
            depth: usize,
        ) -> Result<ValueThunk, String> {
            let Some(scope) = self.ancestor(depth) else {
                return Err(key);
            };
            let result = match scope.borrow_mut().env.entry(key.clone()) {
                Entry::Occupied(mut entry) => {
                    entry.insert(value);
                    Ok(ValueThunk::Thunk {
                        scope: scope.clone(),
                        ident: key,
                    }) // new ver. of optimization (may actually be slower)
                }
                Entry::Vacant(vacant) => Err(vacant.into_key()),
            };
            result
        }
    }

    #[derive(Clone, Debug, ThisError)]
    #[error("Already at global scope")]
    pub struct AtGlobalScopeError;
}

type EvalError = MaybeWithSignal<Located<Error>>;
type StatementEvalResult = Result<(), EvalError>;
type ExpressionEvalResult = Result<Value, EvalError>;
type ExpressionEvalResultThunk = Result<ValueThunk, EvalError>;

pub struct Interpreter {
    environment: Environment,
    globals: Environment,
    locals: HashMap<Location, usize>,
}

impl Interpreter {
    pub fn new() -> Self {
        let globals = Environment::new();
        let mut this = Self {
            environment: globals.clone(),
            globals,
            locals: HashMap::new(),
        };

        // insert native functions into global scope
        this.environment.declare(
            "clock".into(),
            Value::Function(Function {
                arity: 0,
                environment: this.environment.clone(),
                is_initializer: false,
                is_getter: false,
                implementation: FunctionImplementation::Clock,
            }),
        );
        this.environment.declare(
            "deepcopy".into(),
            Value::Function(Function {
                arity: 1,
                environment: this.environment.clone(),
                is_initializer: false,
                is_getter: false,
                implementation: FunctionImplementation::DeepCopy,
            }),
        );
        this.environment.push();
        this
    }

    pub fn list_global_idents(&self) -> Vec<String> {
        self.globals.list_idents()
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
                    .map(|ok| ok.map(ValueThunk::into_owned))?; // return value of function must be owned
                return Err(Error::InvalidReturn
                    .at(location)
                    .signaling(Signal::Return(return_value)));
            }
            Statement::If {
                condition,
                true_branch,
                false_branch,
            } => {
                self.if_statement(condition, true_branch.as_ref(), false_branch.as_ref())
                    .with_maybe_signaled_err_at(Error::IfEvaluation, location)?;
            }
            Statement::While { condition, body } => {
                self.while_statement(condition, body.as_ref())
                    .with_maybe_signaled_err_at(Error::WhileEvaluation, location)?;
            }
            Statement::Print(expression) => {
                let result = self
                    .evaluate(expression)
                    .with_maybe_signaled_err_at(Error::PrintEvaluation, location)?;
                match result.into_owned() {
                    Value::String(s) => println!("{s}"),
                    value => println!("{value}"),
                }
            }
            Statement::Expression(expression) => {
                self.evaluate(expression)
                    .with_maybe_signaled_err_at(Error::ExpressionStatementEvaluation, location)?;
            }
            Statement::Var { name, initializer } => {
                let value = match initializer {
                    Some(expression) => self
                        .evaluate(expression)
                        .with_maybe_signaled_err_at(Error::VarEvaluation, location)?
                        .into_owned(), // own must occur in order to store the value
                    None => Value::Uninitialized,
                };
                self.environment.declare(name.to_owned(), value);
            }
            Statement::Block(statements) => {
                self.environment.push();
                let result = self
                    .block(statements)
                    .with_maybe_signaled_err_at(Error::BlockEvaluation, location);
                self.environment
                    .pop()
                    .expect("Will always have just pushed a scope");
                result?;
            }
            Statement::Function {
                name,
                parameters,
                body,
            } => {
                let function =
                    self.function_declaration(parameters.clone(), body.clone(), false)?;
                self.environment.declare(name.clone(), function);
            }
            Statement::Class {
                name,
                superclass,
                methods,
                class_methods,
            } => {
                self.environment.declare(name.clone(), Value::Nil);
                let class = self.class_declaration(
                    name.clone(),
                    superclass,
                    methods,
                    class_methods,
                    location,
                )?;
                self.environment
                    .assign(name.clone(), class)
                    .expect("We just declared the variable in the current scope");
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
            let condition_value = self.evaluate(condition)?.into_owned();
            (&condition_value).into()
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
            let condition_value = self.evaluate(condition)?.into_owned();
            (&condition_value).into()
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

    pub fn evaluate(&mut self, expression: &Located<Expression>) -> ExpressionEvalResultThunk {
        let location = &expression.location();
        match &expression.item {
            Expression::Literal(literal_token) => self
                .literal(literal_token)
                .with_err_at(Error::InvalidLiteral, location)
                .map_err(MaybeWithSignal::NoSignal)
                .as_thunk(),
            Expression::Variable(name) => self
                .variable(name.to_owned(), location)
                .with_err_at(Error::VariableResolution, location)
                .map_err(MaybeWithSignal::NoSignal)
                .as_thunk(),
            Expression::Assignment {
                variable_name,
                expression,
            } => self
                .assignment(variable_name.clone(), expression) // clone is necessary, because variable reassignment may occur
                .with_maybe_signaled_err_at(Error::AssignmentEvaluation, location),
            Expression::Grouping(sub_expression) => self.evaluate(sub_expression),
            Expression::Unary {
                operator,
                expression,
            } => self
                .unary(operator, expression)
                .with_maybe_signaled_err_at(Error::UnaryEvaluation, location)
                .as_thunk(),
            Expression::Binary {
                operator,
                lhs_expression,
                rhs_expression,
            } => self
                .binary(operator, lhs_expression, rhs_expression)
                .with_maybe_signaled_err_at(Error::BinaryEvaluation, location),
            Expression::Ternary {
                condition,
                true_expression,
                false_expression,
            } => self
                .ternary(condition, true_expression, false_expression)
                .with_maybe_signaled_err_at(Error::TernaryEvaluation, location),
            Expression::Call { callee, arguments } => self
                .call(callee.as_ref(), &arguments[..])
                .with_maybe_signaled_err_at(Error::FunctionCall, location)
                .as_thunk(),
            Expression::Lambda { parameters, body } => self
                .function_declaration(Some(parameters.clone()), body.clone(), false)
                .as_thunk(),
            Expression::Get { object, field } => self.get_expression(object, field).as_thunk(),
            Expression::Set {
                object,
                field,
                value_expression,
            } => self
                .set_expression(object, field, value_expression)
                .as_thunk(),
            Expression::This => self
                .variable(String::from("this"), location)
                .with_err_at(Error::VariableResolution, location)
                .map_err(MaybeWithSignal::NoSignal)
                .as_thunk(),
            Expression::Super(field) => self.super_expression(field, location.clone()).as_thunk(),
        }
    }

    fn function_declaration(
        &mut self,
        parameters: Option<Rc<Vec<Located<String>>>>,
        body: Rc<Located<Statement>>,
        is_initializer: bool,
    ) -> ExpressionEvalResult {
        Ok(Value::Function(Function {
            arity: parameters.as_ref().map(|p| p.len()).unwrap_or(0),
            environment: self.environment.clone(),
            is_initializer,
            is_getter: parameters.is_none(),
            implementation: FunctionImplementation::Lox(parameters.unwrap_or_default(), body), // rc clones, cheap
        }))
    }

    fn class_declaration(
        &mut self,
        name: String,
        superclass_name: &Option<String>,
        method_definitions: &Vec<Located<Statement>>,
        class_method_definitions: &Vec<Located<Statement>>,
        location: &Location,
    ) -> ExpressionEvalResult {
        let superclass = if let Some(superclass_name) = superclass_name {
            let superclass = self
                .variable(superclass_name.clone(), location)
                .map_err(|err| err.at(location).no_signal())?;
            let Value::Class(superclass) = superclass else {
                return Err(Error::InvalidSuperclass(superclass_name.clone())
                    .at(location)
                    .no_signal());
            };
            self.environment.push();
            self.environment
                .declare(String::from("super"), Value::Class(superclass.clone()));
            Some(superclass)
        } else {
            None
        };
        let mut methods = HashMap::new();
        let mut class_methods = HashMap::new();
        for method in method_definitions {
            if let Statement::Function {
                name,
                parameters,
                body,
            } = &method.item
            {
                let method =
                    self.function_declaration(parameters.clone(), body.clone(), name == "init")?;
                methods.insert(name.clone(), method);
            }
        }
        for method in class_method_definitions {
            if let Statement::Function {
                name,
                parameters,
                body,
            } = &method.item
            {
                let method = self.function_declaration(parameters.clone(), body.clone(), false)?;
                class_methods.insert(name.clone(), method);
            }
        }
        if superclass.is_some() {
            self.environment
                .pop()
                .expect("Just pushed a scope for the superclass");
        }
        Ok(Value::Class(Rc::new(Class {
            name,
            superclass,
            methods,
            class_methods,
        })))
    }

    fn literal(&mut self, literal: &Located<Token>) -> Result<Value, Token> {
        literal.item.clone().try_into() // must clone the literal to resolve its value
    }

    fn variable(&mut self, name: String, location: &Location) -> Result<Value, Error> {
        let key = name.clone();
        let depth = self.locals.get(&location);
        match if let Some(&depth) = depth {
            self.environment.get_at(name, depth)
        } else {
            self.globals.get(name)
        } {
            Ok(value) => match value {
                Value::Uninitialized => Err(Error::UninitializedVariable(key)),
                _ => Ok(value),
            },
            Err(key) => Err(Error::UndeclaredVariable(key)),
        }
    }

    fn assignment(
        &mut self,
        name: Located<String>,
        expression: &Located<Expression>,
    ) -> ExpressionEvalResultThunk {
        let (name, location) = name.split();
        let value = self.evaluate(expression)?.into_owned(); // own must occur in order to store the value
        match if let Some(depth) = self.locals.get(&location) {
            self.environment.assign_at(name, value, *depth)
        } else {
            self.globals.assign(name, value)
        } {
            Err(key) => Err(Error::UndeclaredVariable(key).at(&location).no_signal()),
            Ok(value) => Ok(value),
        }
    }

    fn unary(
        &mut self,
        unary: &Located<Token>,
        unary_expr: &Located<Expression>,
    ) -> ExpressionEvalResult {
        let location = unary.location();
        let value = self.evaluate(unary_expr)?;
        match (&unary.item, value.into_owned()) {
            (Token::Minus, Value::Number(value)) => Ok(Value::Number(-value)),
            (Token::Bang, operand) => {
                let bool_value: bool = (&operand).into();
                Ok((!bool_value).into())
            }
            (unary, value) => Err(Error::InvalidUnary(unary.clone(), value)
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
    ) -> ExpressionEvalResultThunk {
        let binary_location = binary.location();
        let lhs_location = lhs_expr.location();

        let lhs_value = self.evaluate(lhs_expr)?.into_owned();

        let lhs_truthiness = match ((&lhs_value).into(), &binary.item) {
            (false, Token::And) | (true, Token::Or) => return Ok(ValueThunk::Value(lhs_value)),
            (lhs_truthiness, _) => lhs_truthiness,
        };

        let rhs_value = self.evaluate(rhs_expr)?;

        // finish short circuit boolean evaluation
        match (lhs_truthiness, &binary.item) {
            (true, Token::And) | (false, Token::Or) => {
                return Ok(rhs_value);
            }
            _ => (),
        }

        match (lhs_value, &binary.item, rhs_value.into_owned()) {
            // equality
            (lhs, Token::EqualEqual, rhs) => Ok(ValueThunk::Value((lhs == rhs).into())),
            (lhs, Token::BangEqual, rhs) => Ok(ValueThunk::Value((lhs != rhs).into())),

            // comparison
            (Value::Number(lhs), Token::Less, Value::Number(rhs)) => {
                Ok(ValueThunk::Value((lhs < rhs).into()))
            }
            (Value::Number(lhs), Token::LessEqual, Value::Number(rhs)) => {
                Ok(ValueThunk::Value((lhs <= rhs).into()))
            }
            (Value::Number(lhs), Token::Greater, Value::Number(rhs)) => {
                Ok(ValueThunk::Value((lhs > rhs).into()))
            }
            (Value::Number(lhs), Token::GreaterEqual, Value::Number(rhs)) => {
                Ok(ValueThunk::Value((lhs >= rhs).into()))
            }
            (Value::String(lhs), Token::Less, Value::String(rhs)) => {
                Ok(ValueThunk::Value((lhs < rhs).into()))
            }
            (Value::String(lhs), Token::LessEqual, Value::String(rhs)) => {
                Ok(ValueThunk::Value((lhs <= rhs).into()))
            }
            (Value::String(lhs), Token::Greater, Value::String(rhs)) => {
                Ok(ValueThunk::Value((lhs > rhs).into()))
            }
            (Value::String(lhs), Token::GreaterEqual, Value::String(rhs)) => {
                Ok(ValueThunk::Value((lhs >= rhs).into()))
            }

            // arithmetic
            (lhs_value, Token::Slash, Value::Number(rhs)) if rhs.borrow() == &0.0 => {
                Err(Error::DivisionByZero(lhs_value)
                    .at(&lhs_location)
                    .no_signal())
            }
            (Value::Number(lhs), Token::Minus, Value::Number(rhs)) => {
                Ok(ValueThunk::Value(Value::Number(lhs - rhs)))
            }
            (Value::Number(lhs), Token::Plus, Value::Number(rhs)) => {
                Ok(ValueThunk::Value(Value::Number(lhs + rhs)))
            }
            (Value::Number(lhs), Token::Star, Value::Number(rhs)) => {
                Ok(ValueThunk::Value(Value::Number(lhs * rhs)))
            }
            (Value::Number(lhs), Token::Slash, Value::Number(rhs)) => {
                Ok(ValueThunk::Value(Value::Number(lhs / rhs)))
            }

            // string concatenation
            (Value::String(lhs), Token::Plus, Value::String(rhs)) => {
                Ok(ValueThunk::Value(Value::String(format!("{lhs}{rhs}"))))
            }
            (Value::String(lhs), Token::Plus, rhs) => {
                Ok(ValueThunk::Value(Value::String(format!("{lhs}{rhs}"))))
            }
            (lhs, Token::Plus, Value::String(rhs)) => {
                Ok(ValueThunk::Value(Value::String(format!("{lhs}{rhs}"))))
            }

            // string cycling
            (Value::String(string), Token::Star, Value::Number(quantity))
            | (Value::Number(quantity), Token::Star, Value::String(string)) => Ok(
                ValueThunk::Value(Value::String(string.repeat(quantity as usize))),
            ),

            // invalid
            (lhs_value, operator, rhs_value) => {
                Err(Error::InvalidBinary(lhs_value, operator.clone(), rhs_value)
                    .at(&binary_location)
                    .no_signal()) // error contents must be owned
            }
        }
    }

    fn ternary(
        &mut self,
        condition_expr: &Located<Expression>,
        true_branch_expr: &Located<Expression>,
        false_branch_expr: &Located<Expression>,
    ) -> ExpressionEvalResultThunk {
        let condition_value = self.evaluate(condition_expr)?.into_owned();
        if (&condition_value).into() {
            self.evaluate(true_branch_expr)
        } else {
            self.evaluate(false_branch_expr)
        }
    }

    pub fn resolve(&mut self, location: Location, i: usize) {
        self.locals.insert(location, i);
    }

    pub fn get_expression(
        &mut self,
        sub_expression: &Located<Expression>,
        field: &Located<String>,
    ) -> ExpressionEvalResult {
        match self.evaluate(sub_expression)?.into_owned() {
            Value::Instance(instance) => {
                let value = instance.get(self, &field)?;
                Ok(value)
            }
            Value::Class(class) => {
                let Some(method) = class.class_methods.get(&field.item).cloned() else {
                    return Err(Error::InvalidFieldAccess(field.item.clone())
                        .at(&field.location())
                        .no_signal());
                };
                Ok(method)
            }
            _ => Err(Error::GetOnNonObject.at(&field.location()).no_signal()),
        }
    }

    pub fn set_expression(
        &mut self,
        assignment_expression: &Located<Expression>,
        field: &Located<String>,
        value_expression: &Located<Expression>,
    ) -> ExpressionEvalResult {
        let Value::Instance(instance) = self.evaluate(assignment_expression)?.into_owned() else {
            return Err(Error::SetOnNonObject.at(&field.location()).no_signal());
        };
        let value = self.evaluate(value_expression)?.into_owned();
        RefCell::borrow_mut(&instance).set(&field, value.clone())?;
        Ok(value)
    }

    pub fn super_expression(
        &mut self,
        field: &Located<String>,
        location: Location,
    ) -> ExpressionEvalResult {
        let depth = self
            .locals
            .get(&location)
            .expect("superclass is always accessible from super call");
        let Ok(Value::Class(superclass)) = self.environment.get_at("super".to_owned(), *depth)
        else {
            unreachable!("superclass is always accessible from super call");
        };
        let Ok(Value::Instance(this)) = self.environment.get_at("this".to_owned(), *depth - 1)
        else {
            unreachable!("this is always accessible from super call");
        };
        let Some(Value::Function(mut method)) = superclass.find_method(&field.item) else {
            return Err(Error::InvalidFieldAccess(field.item.clone())
                .at(&field.location())
                .no_signal());
        };
        this.bind(&mut method);
        Ok(Value::Function(method))
    }
}

#[cfg(test)]
mod tests {
    use super::{Environment, Value};

    #[test]
    fn test() {
        let mut env = Environment::new();
        env.declare("x".to_owned(), Value::Number(5.0));
        env.declare("y".to_owned(), Value::Number(10.0));
        env.push();
        let _ = env.assign("x".to_owned(), Value::Number(40.0));
        env.declare("z".to_owned(), Value::Number(607.0));
        dbg!(&env);
        env.declare("x".to_owned(), Value::Number(900.0));
        dbg!(&env);
        env.pop().unwrap();
        let _ = env.assign("x".to_owned(), Value::Number(18.0));
        dbg!(&env);
    }
}
