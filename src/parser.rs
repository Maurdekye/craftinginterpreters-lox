use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

use thiserror::Error as ThisError;

use crate::{
    lexer::Token,
    util::{
        AppendMaybeLocatedError, Errors, Indent, Locateable, Located, LocatedAt, Location,
        MaybeLocated, MaybeLocatedAt, Peekable,
    },
};

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("In this for loop:\n{0}")]
    ForParse(Box<MaybeLocated<Error>>),
    #[error("In this while loop:\n{0}")]
    WhileParse(Box<MaybeLocated<Error>>),
    #[error("In this if statement:\n{0}")]
    IfParse(Box<MaybeLocated<Error>>),
    #[error("In this print statement:\n{0}")]
    PrintParse(Box<MaybeLocated<Error>>),
    #[error("In this var statement:\n{0}")]
    VarParse(Box<MaybeLocated<Error>>),
    #[error("In this block:\n{0}")]
    BlockParse(Errors<MaybeLocated<Error>>),
    #[error("In this statement:\n{0}")]
    ExpressionStatementParse(Box<MaybeLocated<Error>>),
    #[error("In this function declaration:\n{0}")]
    FunctionDeclarationParse(Box<MaybeLocated<Error>>),
    #[error("In this class declaration:\n{0}")]
    ClassDeclarationParse(Errors<MaybeLocated<Error>>),

    #[error("In this ternary:\n{0}")]
    TernaryParse(Box<MaybeLocated<Error>>),
    #[error("In this binary expression:\n{0}")]
    BinaryParse(Box<MaybeLocated<Error>>),
    #[error("At this unary operator:\n{0}")]
    UnaryParse(Box<MaybeLocated<Error>>),
    #[error("In this assignment:\n{0}")]
    AssignmentParse(Box<MaybeLocated<Error>>),

    #[error("Was looking for a '{0}', but got a '{1}' instead")]
    UndesiredToken(Token, Token),
    #[error(
        "Was expecting a comma or closing paren while reading function arguments, but got a '{0}'"
    )]
    UnexpectedArgumentToken(Token),
    #[error("Where's the class name?")]
    MissingClassName,
    #[error("Where's the function name?")]
    MissingFunctionName,
    #[error("Where's the variable name?")]
    MissingVarIdentifier,
    #[error("You forgot a semicolon")]
    MissingSemicolon,
    #[error("That's not a variable name")]
    InvalidAssignmentTarget(Expression),
    #[error("File's ended")]
    UnexpectedEndOfTokenStream,
    #[error("You forgot a ')' for the '(' at [{0}:{1}]")]
    UnclosedOpeningParen(usize, usize),
    #[error("What's '{0}' mean?")]
    UnexpectedToken(Token),
    #[error("This '=' doesnt make sense here, it's supposed to come after a variable name in an assignment")]
    UnexpectedAssignmentOperator,
    #[error("This '{0}' doesn't make sense here, it's supposed to be used in some sort of binary expression")]
    UnexpectedBinaryOperator(Token),
    #[error("This '{0}' doesn't make sense here, it's supposed to be part of a ternary")]
    UnexpectedTernaryOperator(Token),
    #[error("Function calls can't have more than 255 arguments")]
    TooManyArguments,
    #[error("Function parameters should be identifiers, not '{0}'")]
    UnexpectedFunctionParameter(Token),
    #[error("Expected identifier after '.'")]
    MissingIdentifierInGet,
}

#[derive(Clone, Debug)]
pub enum Expression {
    Literal(Located<Token>),
    Variable(String),
    Assignment(Located<String>, Box<Located<Expression>>),
    Grouping(Box<Located<Expression>>),
    Unary(Located<Token>, Box<Located<Expression>>),
    Binary(
        Located<Token>,
        Box<Located<Expression>>,
        Box<Located<Expression>>,
    ),
    Ternary(
        Box<Located<Expression>>,
        Box<Located<Expression>>,
        Box<Located<Expression>>,
    ),
    Call(Box<Located<Expression>>, Vec<Located<Expression>>),
    Get(Box<Located<Expression>>, Located<String>),
    Set(
        Box<Located<Expression>>,
        Located<String>,
        Box<Located<Expression>>,
    ),
    Lambda(Rc<Vec<Located<String>>>, Rc<Located<Statement>>),
    This,
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Literal(Located { item: token, .. }) => write!(f, "{token}"),
            Expression::Variable(name) => write!(f, "(ref {name})"),
            Expression::Assignment(name, expr) => write!(f, "(var {name} {expr})"),
            Expression::Grouping(expr) => write!(f, "(group {})", expr.item),
            Expression::Unary(Located { item: token, .. }, expr) => write!(f, "({token} {expr})"),
            Expression::Binary(Located { item: token, .. }, lhs, rhs) => {
                write!(f, "({token} {lhs} {rhs})")
            }
            Expression::Ternary(condition, true_expr, false_expr) => {
                write!(
                    f,
                    "(? {} {} {})",
                    condition.item, true_expr.item, false_expr.item
                )
            }
            Expression::Call(callee, args) => {
                write!(
                    f,
                    "({} {})",
                    callee.item,
                    args.iter()
                        .map(|a| format!("{a}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            Expression::Get(subexpr, field) => {
                write!(f, "(get {} {})", subexpr.item, field.item)
            }
            Expression::Set(instance_expr, field, value_expr) => {
                write!(
                    f,
                    "(set {} {} {})",
                    instance_expr.item, field.item, value_expr.item
                )
            }
            Expression::Lambda(args, body) => {
                write!(
                    f,
                    "(lambda ({}) {})",
                    args.iter()
                        .map(|a| a.item.clone())
                        .collect::<Vec<_>>()
                        .join(" "),
                    body.item
                )
            }
            Expression::This => write!(f, "this"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Statement {
    Class(String, Vec<Located<Statement>>, Vec<Located<Statement>>),
    Function(
        String,
        Option<Rc<Vec<Located<String>>>>,
        Rc<Located<Statement>>,
    ),
    Print(Located<Expression>),
    Expression(Located<Expression>),
    Var(String, Option<Located<Expression>>),
    Block(Vec<Located<Statement>>),
    If(
        Located<Expression>,
        Box<Located<Statement>>,
        Box<Option<Located<Statement>>>,
    ),
    While(Located<Expression>, Box<Located<Statement>>),
    Break,
    Continue,
    Return(Option<Located<Expression>>),
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Class(name, methods, class_methods) => {
                writeln!(f, "(class {}", name)?;
                for function in methods.iter().chain(class_methods) {
                    writeln!(f, "{}", function.indented(2))?;
                }
                writeln!(f, ")")
            }
            Statement::Function(name, args, body) => {
                writeln!(
                    f,
                    "(fun {} ({}) {})",
                    name,
                    args.as_ref().map(|a| a
                        .iter()
                        .map(|a| a.item.clone())
                        .collect::<Vec<_>>()
                        .join(" "))
                        .unwrap_or(String::new()),
                    body.item
                )
            }
            Statement::Print(expression) => writeln!(f, "(print {})", expression.item),
            Statement::Expression(expression) => writeln!(f, "{}", expression.item),
            Statement::Var(name, None) => {
                writeln!(f, "(var {})", name)
            }
            Statement::Var(name, Some(expression)) => {
                writeln!(f, "(var {} {})", name, expression.item)
            }
            Statement::Block(statements) => {
                writeln!(f, "(block")?;
                for statement in statements {
                    write!(f, "{}", statement.item.indented(2))?;
                }
                writeln!(f, ")")
            }
            Statement::If(condition, true_branch, false_branch) => {
                writeln!(f, "(if {condition}")?;
                write!(f, "{}", true_branch.indented(2))?;
                if let Some(false_branch) = false_branch.as_ref() {
                    write!(f, "{}", false_branch.indented(2))?;
                }
                writeln!(f, ")")
            }
            Statement::While(condition, body) => {
                writeln!(f, "(while {condition}")?;
                write!(f, "{}", body.indented(2))?;
                writeln!(f, ")")
            }
            Statement::Break => {
                writeln!(f, "break")
            }
            Statement::Continue => {
                writeln!(f, "continue")
            }
            Statement::Return(value) => match value {
                Some(value) => writeln!(f, "(return {})", value.item),
                None => writeln!(f, "return"),
            },
        }
    }
}

type ExpressionParseResult = Result<Located<Expression>, MaybeLocated<Error>>;
type StatementParseResult = Result<Located<Statement>, MaybeLocated<Error>>;
type StatementParseResultErrors = Result<Located<Statement>, Errors<MaybeLocated<Error>>>;

macro_rules! consume_token {
    ($this:ident, $token:ident) => {
        $this.consume(
            |t| matches!(t, $crate::lexer::Token::$token),
            |t| $crate::parser::Error::UndesiredToken($crate::lexer::Token::$token, t),
        )
    };
}

macro_rules! split_some {
    ($match_expr:expr => |$item:ident, $location:ident| $body:block) => {
        match $match_expr {
            Some(located) => {
                let $location = located.location();
                let $item = located.item;
                $body
            }
            None => return $crate::parser::end_of_stream(),
        }
    };
}

macro_rules! split_ref_some {
    ($match_expr:expr => |$item:ident, $location:ident| $body:block) => {
        match $match_expr {
            Some(located) => {
                let $location = &located.location();
                let $item = &located.item;
                $body
            }
            None => return $crate::parser::end_of_stream(),
        }
    };
}

macro_rules! split_ref_some_errors {
    ($match_expr:expr => |$item:ident, $location:ident| $body:block) => {
        match $match_expr {
            Some(located) => {
                let $location = &located.location();
                let $item = &located.item;
                $body
            }
            None => {
                return $crate::parser::end_of_stream()
                    .map_err(|e| $crate::util::Errors::from_iter(::std::iter::once(e)))
            }
        }
    };
}

fn end_of_stream<T>() -> Result<T, MaybeLocated<Error>> {
    Err(Error::UnexpectedEndOfTokenStream.unlocated())
}

pub struct Parser<I>
where
    I: Iterator,
{
    tokens: Peekable<I>,
}

impl<I> Parser<I>
where
    I: Iterator<Item = Located<Token>>,
{
    // constructor
    pub fn new(tokens: I) -> Self {
        Self {
            tokens: Peekable::new(tokens),
        }
    }

    // utility fns
    fn synchronize(&mut self) {
        while let Some(_) = self.tokens.next_if(|token| {
            !matches!(
                token.item,
                Token::Semicolon
                    | Token::Class
                    | Token::Fun
                    | Token::Var
                    | Token::For
                    | Token::If
                    | Token::While
                    | Token::Print
                    | Token::Return
            )
        }) {}
        self.tokens
            .next_if(|token| matches!(token.item, Token::Semicolon));
    }

    fn consume(
        &mut self,
        pred: impl FnOnce(&Token) -> bool,
        error_factory: impl FnOnce(Token) -> Error,
    ) -> Result<Located<Token>, MaybeLocated<Error>> {
        self.tokens
            .next_if(|t| pred(&t.item))
            .ok_or_else(|| match self.tokens.peek() {
                Some(token) => {
                    let location = token.location();
                    error_factory(token.item.clone()).located_at(&location)
                }
                None => error_factory(Token::Eof).unlocated(),
            })
    }

    fn consume_semicolon(&mut self) -> Result<Location, MaybeLocated<Error>> {
        self.consume(
            |t| matches!(t, Token::Semicolon),
            |_| Error::MissingSemicolon,
        )
        .map(|x| x.location())
    }

    fn consume_identifier(
        &mut self,
        error_factory: impl FnOnce(Token) -> Error,
    ) -> Result<Located<String>, MaybeLocated<Error>> {
        split_ref_some!(self.tokens.peek() => |token, location| {
            match token {
                Token::Identifier(_) => {
                    let Some((Token::Identifier(name), location)) = self.tokens.next().map(Located::split) else {
                        unreachable!();
                    };
                    Ok(name.at(&location))
                }
                _ => Err(error_factory(token.clone()).located_at(location).into())
            }
        })
    }

    // parsing fns
    pub fn parse(&mut self) -> Result<Vec<Located<Statement>>, Errors<MaybeLocated<Error>>> {
        let mut statements = Vec::new();
        let mut errors = Errors::new();

        loop {
            split_ref_some_errors!(self.tokens.peek() => |token, _location| {
                match token {
                    Token::Eof => break,
                    _ => match self.declaration() {
                        Ok(statement) => statements.push(statement),
                        Err(err) => {
                            errors.push(err);
                            self.synchronize();
                        }
                    }
                }
            });
        }

        errors.empty_ok(statements)
    }

    fn declaration(&mut self) -> StatementParseResult {
        split_ref_some!(self.tokens.peek() => |token, location| {
            match token {
                Token::Var => self.var(location).with_err_located_at(Error::VarParse, location),
                Token::Fun => self.function(location).with_err_located_at(Error::FunctionDeclarationParse, location),
                Token::Class => self.class(location).with_err_located_at(Error::ClassDeclarationParse, location),
                _ => self.statement(),
            }
        })
    }

    fn var(&mut self, _location: &impl Locateable) -> StatementParseResult {
        self.tokens.next();
        let name = self
            .consume_identifier(|_| Error::MissingVarIdentifier)?
            .item;

        split_some!(self.tokens.next() => |token, location| {
            match token {
                Token::Semicolon => Ok(Statement::Var(name, None).at(&location)),
                Token::Equal => {
                    let var_expr = self.expression()?;
                    self.consume_semicolon()?;
                    Ok(Statement::Var(name, Some(var_expr)).at(&location))
                }
                other => Err(Error::UnexpectedToken(other).located_at(&location)),
            }
        })
    }

    fn function_parameters(&mut self) -> Result<Vec<Located<String>>, MaybeLocated<Error>> {
        consume_token!(self, LeftParen)?;
        let mut parameters = Vec::new();
        if self
            .tokens
            .next_if(|t| matches!(t.item, Token::RightParen))
            .is_none()
        {
            loop {
                let parameter = self.consume_identifier(Error::UnexpectedFunctionParameter)?;
                parameters.push(parameter);
                split_some!(self.tokens.next() => |token, location| {
                    match token {
                        Token::Comma => {
                            if parameters.len() >= 255 {
                                return Err(Error::TooManyArguments.located_at(&location))
                            }
                        },
                        Token::RightParen => break,
                        other => {
                            return Err(Error::UnexpectedArgumentToken(other).located_at(&location))
                        }
                    }
                });
            }
        }
        Ok(parameters)
    }

    fn function(&mut self, location: &impl Locateable) -> StatementParseResult {
        self.tokens.next();
        self.method(false, location)
    }

    fn method(&mut self, allow_getter: bool, location: &impl Locateable) -> StatementParseResult {
        let name = self
            .consume_identifier(|_| Error::MissingFunctionName)?
            .item;
        split_ref_some!(self.tokens.peek() => |token, params_location| {
            match token {
                Token::LeftParen => {
                    let parameters = self.function_parameters()?;
                    let body = self.statement()?;
                    Ok(Statement::Function(name, Some(parameters.into()), body.into()).at(location))
                }
                _ if allow_getter => {
                    let body = self.statement()?;
                    Ok(Statement::Function(name, None, body.into()).at(location))
                }
                token => Err(Error::UnexpectedToken(token.clone()).located_at(params_location))
            }
        })
    }

    fn class(&mut self, location: &impl Locateable) -> StatementParseResultErrors {
        self.tokens.next();
        let name = self.consume_identifier(|_| Error::MissingClassName)?.item;
        consume_token!(self, LeftBrace)?;
        let mut methods = Vec::new();
        let mut class_methods = Vec::new();
        let mut errors = Errors::new();
        loop {
            split_ref_some_errors!(self.tokens.peek() => |token, location| {
                match token {
                    Token::RightBrace => {
                        self.tokens.next();
                        break;
                    }
                    Token::Eof => {
                        errors.push(
                            Error::UndesiredToken(Token::RightBrace, Token::Eof).located_at(location),
                        );
                        break;
                    }
                    Token::Class => {
                        self.tokens.next();
                        match self.method(false, location) {
                            Ok(function) => class_methods.push(function.into()),
                            Err(err) => {
                                errors.push(err);
                                self.synchronize();
                            }
                        }
                    }
                    _ => {
                        match self.method(true, location) {
                            Ok(function) => methods.push(function.into()),
                            Err(err) => {
                                errors.push(err);
                                self.synchronize();
                            }
                        }
                    }
                }
            });
        }
        errors.empty_ok(Statement::Class(name, methods, class_methods).at(location))
    }

    fn statement(&mut self) -> StatementParseResult {
        split_ref_some!(self.tokens.peek() => |token, location| {
            match token {
                Token::Break => {
                    self.tokens.next();
                    self.consume_semicolon()?;
                    Ok(Statement::Break.at(location))
                }
                Token::Continue => {
                    self.tokens.next();
                    self.consume_semicolon()?;
                    Ok(Statement::Continue.at(location))
                }
                Token::Return => {
                    self.tokens.next();
                    let value = if self.consume_semicolon().is_err() {
                        let expression = self.expression()?;
                        self.consume_semicolon()?;
                        Some(expression)
                    } else {
                        None
                    };
                    Ok(Statement::Return(value).at(location))
                }
                Token::If => self.if_statement(location).with_err_located_at(Error::IfParse, location),
                Token::While => {
                    self.while_statement(location).with_err_located_at(Error::WhileParse, location)
                }
                Token::For => {
                    self.for_statement(location).with_err_located_at(Error::ForParse, location)
                }
                Token::Print => self.print(location).with_err_located_at(Error::PrintParse, location),
                Token::LeftBrace => {
                    self.block(location).with_err_located_at(Error::BlockParse, location)
                }
                _ => self.expression_statement()
                    .with_err_located_at(Error::ExpressionStatementParse, location),
            }
        })
    }

    fn if_statement(&mut self, location: &impl Locateable) -> StatementParseResult {
        self.tokens.next();
        let condition = self.expression()?;
        let true_branch = self.statement()?;
        let false_branch = if let Some(_) = self.tokens.next_if(|t| matches!(t.item, Token::Else)) {
            Some(self.statement()?)
        } else {
            None
        };
        Ok(Statement::If(condition, true_branch.into(), false_branch.into()).at(location))
    }

    fn while_statement(&mut self, location: &impl Locateable) -> StatementParseResult {
        self.tokens.next();
        let condition = self.expression()?;
        let body = self.statement()?;
        Ok(Statement::While(condition, body.into()).at(location))
    }

    fn for_statement(&mut self, location: &impl Locateable) -> StatementParseResult {
        self.tokens.next();
        consume_token!(self, LeftParen)?;

        // parse individual pieces
        let initializer = split_ref_some!(self.tokens.peek() => |token, location| {
            match token {
                Token::Semicolon => {
                    self.tokens.next();
                    None
                }
                Token::Var => Some(self.var(location)?),
                _ => Some(self.expression_statement()?),
            }
        });
        let condition = if self
            .tokens
            .next_if(|t| matches!(t.item, Token::Semicolon))
            .is_none()
        {
            let condition = Some(self.expression()?);
            self.consume_semicolon()?;
            condition
        } else {
            None
        };
        let increment = if self
            .tokens
            .next_if(|t| matches!(t.item, Token::RightParen))
            .is_none()
        {
            let increment = Some(self.expression()?);
            consume_token!(self, RightParen)?;
            increment
        } else {
            None
        };
        let mut body = self.statement()?;

        // construct final ast
        if let Some(increment) = increment {
            let increment_location = increment.location();
            body = Statement::Block(vec![
                body,
                Statement::Expression(increment).at(&increment_location),
            ])
            .at(location);
        }
        let condition =
            condition.unwrap_or(Expression::Literal(Token::True.at(location)).at(location));
        let mut loop_body = Statement::While(condition, Box::new(body)).at(location);
        if let Some(initializer) = initializer {
            loop_body = Statement::Block(vec![initializer, loop_body]).at(location);
        }
        Ok(loop_body)
    }

    fn print(&mut self, location: &impl Locateable) -> StatementParseResult {
        self.tokens.next();
        let expr = self.expression()?;
        self.consume_semicolon()?;
        Ok(Statement::Print(expr).at(location))
    }

    fn block(&mut self, location: &impl Locateable) -> StatementParseResultErrors {
        self.tokens.next();
        let mut statements = Vec::new();
        let mut errors = Errors::new();
        loop {
            split_ref_some_errors!(self.tokens.peek() => |token, location| {
                match token {
                    Token::RightBrace => {
                        self.tokens.next();
                        break;
                    }
                    Token::Eof => {
                        errors.push(
                            Error::UndesiredToken(Token::RightBrace, Token::Eof).located_at(location),
                        );
                        break;
                    }
                    _ => match self.declaration() {
                        Ok(statement) => statements.push(statement),
                        Err(err) => {
                            errors.push(err);
                            self.synchronize();
                        }
                    },
                }
            });
        }
        errors.empty_ok(Statement::Block(statements).at(location))
    }

    fn expression_statement(&mut self) -> StatementParseResult {
        let expr = self.expression()?;
        let location = expr.location();
        self.consume_semicolon()?;
        Ok(Statement::Expression(expr).at(&location))
    }

    pub fn expression(&mut self) -> ExpressionParseResult {
        split_ref_some!(self.tokens.peek() => |token, location| {
            match token {
                Token::Fun => self.lambda(location),
                _ => self.assignment()
            }
        })
    }

    fn lambda(&mut self, location: &impl Locateable) -> ExpressionParseResult {
        self.tokens.next();
        let parameters = self.function_parameters()?;
        let body = self.statement()?;
        Ok(Expression::Lambda(parameters.into(), body.into()).at(location))
    }

    fn assignment(&mut self) -> ExpressionParseResult {
        if let Some(operator) = self
            .tokens
            .next_if(|token| matches!(token.item, Token::Equal))
        {
            return Err(Error::UnexpectedAssignmentOperator.located_at(&operator));
        }
        let mut expression = self.ternary()?;
        if let Some(_) = self
            .tokens
            .next_if(|token| matches!(token.item, Token::Equal))
        {
            let target_location = expression.location();
            expression = self
                .assignment_expression(expression)
                .with_err_located_at(Error::AssignmentParse, &target_location)?;
        }
        Ok(expression)
    }

    fn assignment_expression(&mut self, expression: Located<Expression>) -> ExpressionParseResult {
        let (expression, ident_location) = expression.split();
        match expression {
            Expression::Variable(name) => {
                let rhs_expression = self.assignment()?;
                Ok(
                    Expression::Assignment(name.at(&ident_location), rhs_expression.into())
                        .at(&ident_location),
                )
            }
            Expression::Get(sub_expr, field) => {
                let rhs_expression = self.assignment()?;
                Ok(Expression::Set(sub_expr, field, rhs_expression.into()).at(&ident_location))
            }
            _ => Err(Error::InvalidAssignmentTarget(expression).located_at(&ident_location)),
        }
    }

    fn ternary(&mut self) -> ExpressionParseResult {
        if let Some(operator) = self.tokens.next_if(|token: &Located<Token>| {
            matches!(token.item, Token::QuestionMark | Token::Colon)
        }) {
            return Err(
                Error::UnexpectedTernaryOperator(operator.item.clone()).located_at(&operator)
            );
        }
        let mut expression = self.binary()?;
        while let Some(operator) = self
            .tokens
            .next_if(|token| matches!(token.item, Token::QuestionMark))
        {
            expression = self
                .ternary_body(expression)
                .with_err_located_at(Error::TernaryParse, &operator)?;
        }
        Ok(expression)
    }

    fn ternary_body(&mut self, expression: Located<Expression>) -> ExpressionParseResult {
        let true_expr = self.binary()?;
        consume_token!(self, Colon)?;
        let false_expr = self.binary()?;
        let location = expression.location();
        Ok(
            Expression::Ternary(expression.into(), true_expr.into(), false_expr.into())
                .at(&location),
        )
    }

    fn binary_parse<F>(
        &mut self,
        operator_pred: impl Fn(&Token) -> bool,
        mut sub_parser: F,
    ) -> ExpressionParseResult
    where
        F: FnMut(&mut Self) -> ExpressionParseResult,
    {
        if let Some(operator) = self
            .tokens
            .next_if(|token| operator_pred(&token.item) && !matches!(token.item, Token::Minus))
        {
            return Err(
                Error::UnexpectedBinaryOperator(operator.item.clone()).located_at(&operator)
            );
        }
        let mut expression = sub_parser(self)?;
        while let Some(operator) = self.tokens.next_if(|token| operator_pred(&token.item)) {
            let rhs_expression =
                sub_parser(self).with_err_located_at(Error::BinaryParse, &operator)?;
            let location = expression.location();
            expression = Expression::Binary(operator, expression.into(), rhs_expression.into())
                .at(&location);
        }
        Ok(expression)
    }

    fn binary(&mut self) -> ExpressionParseResult {
        self.binary_parse(
            |t| matches!(t, Token::Or),
            |this| {
                this.binary_parse(
                    |t: &Token| matches!(t, Token::And),
                    |this| {
                        this.binary_parse(
                            |t| matches!(t, Token::EqualEqual | Token::BangEqual),
                            |this| {
                                this.binary_parse(
                                    |t| {
                                        matches!(
                                            t,
                                            Token::Greater
                                                | Token::GreaterEqual
                                                | Token::Less
                                                | Token::LessEqual
                                        )
                                    },
                                    |this| {
                                        this.binary_parse(
                                            |t| matches!(t, Token::Minus | Token::Plus),
                                            |this| {
                                                this.binary_parse(
                                                    |t| matches!(t, Token::Slash | Token::Star),
                                                    Parser::unary,
                                                )
                                            },
                                        )
                                    },
                                )
                            },
                        )
                    },
                )
            },
        )
    }

    fn unary(&mut self) -> ExpressionParseResult {
        if let Some(operator) = self
            .tokens
            .next_if(|token| matches!(token.item, Token::Bang | Token::Minus))
        {
            let location = operator.location();
            let rhs = self
                .call()
                .with_err_located_at(Error::UnaryParse, &location)?;
            Ok(Expression::Unary(operator, rhs.into()).at(&location))
        } else {
            self.call()
        }
    }

    fn call(&mut self) -> ExpressionParseResult {
        let mut expr = self.primary()?;
        loop {
            split_ref_some!(self.tokens.peek() => |token, location| {
                match token {
                    Token::LeftParen => {
                        self.tokens.next();
                        let mut args = Vec::new();
                        if self
                            .tokens
                            .next_if(|t| matches!(t.item, Token::RightParen))
                            .is_none()
                        {
                            loop {
                                args.push(self.expression()?);
                                split_some!(self.tokens.next() => |token, location| {
                                    match token {
                                        Token::Comma => {
                                            if args.len() >= 255 {
                                                return Err(Error::TooManyArguments.located_at(&location))
                                            }
                                        },
                                        Token::RightParen => break,
                                        other => {
                                            return Err(Error::UnexpectedArgumentToken(other).located_at(&location))
                                        }
                                    }
                                });
                            }
                        }
                        expr = Expression::Call(Box::new(expr), args).at(location);
                    }
                    Token::Dot => {
                        self.tokens.next();
                        let field = self.consume_identifier(|_| Error::MissingIdentifierInGet)?;
                        let expr_location = expr.location();
                        expr = Expression::Get(expr.into(), field).at(&expr_location)
                    }
                    _ => break
                }
            });
        }
        Ok(expr)
    }

    fn primary(&mut self) -> ExpressionParseResult {
        let Some(next_token) = self.tokens.next() else {
            return end_of_stream();
        };
        let location = next_token.location();

        match next_token.item {
            Token::False | Token::True | Token::Nil | Token::Number(_) | Token::String(_) => {
                Ok(Expression::Literal(next_token).at(&location))
            }
            Token::This => Ok(Expression::This.at(&location)),
            Token::Identifier(name) => Ok(Expression::Variable(name).at(&location)),
            Token::LeftParen => {
                let sub_expression = self.expression()?;
                let close_token = self.tokens.next();
                let Some(Located {
                    item: Token::RightParen,
                    ..
                }) = close_token
                else {
                    return Err(
                        Error::UnclosedOpeningParen(next_token.line, next_token.character)
                            .located_if(close_token.as_ref()),
                    );
                };
                Ok(Expression::Grouping(sub_expression.into()).at(&location))
            }
            _ => Err(Error::UnexpectedToken(next_token.item.clone()).located_at(&next_token)),
        }
    }
}
