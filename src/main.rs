use std::{
    io::{self, stdin, stdout, Write},
    iter,
    path::PathBuf,
    process::{ExitCode, Termination},
};

use interpreter::{MaybeWithSignal, Value};
use lexer::Tokens;
use thiserror::Error as ThisError;

use clap::Parser;
use util::{ErrorInto, Errors, Located, MaybeLocated};

use crate::{interpreter::Interpreter, util::ErrorsInto};

mod interpreter;
mod lexer;
mod parser;
mod resolver;
mod util;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Lexer Error: {0}")]
    Lexer(#[from] Located<lexer::Error>),
    #[error("Parser Error:\n{0}")]
    Parser(#[from] MaybeLocated<parser::Error>),
    #[error("Resolver Error:\n{0}")]
    Resolver(#[from] Located<resolver::Error>),
    #[error("Interpreter Error:\n{0}")]
    Interpreter(#[from] Located<interpreter::Error>),
}

impl Termination for Error {
    fn report(self) -> ExitCode {
        match self {
            Error::Interpreter(_) => ExitCode::from(70),
            _ => ExitCode::from(65),
        }
    }
}

#[derive(Debug, ThisError)]
pub enum RootError {
    #[error("IO: {0}")]
    IO(#[from] io::Error),
    #[error("Lox {0}")]
    Lox(#[from] Errors<Error>),
}

impl Termination for RootError {
    fn report(self) -> std::process::ExitCode {
        match self {
            RootError::IO(_) => ExitCode::FAILURE,
            RootError::Lox(root_error) => root_error.report(),
        }
    }
}

/// Interpret lox code, evaluating and printing the execution result,
/// and then return a list of any errors that may have been encountered
fn run_with(source: String, interpreter: &mut Interpreter) -> Result<(), Errors<Error>> {
    let mut errors = Errors::new();
    let mut raw_tokens = Tokens::from(&*source);
    let tokens = iter::from_fn(|| loop {
        match raw_tokens.next() {
            Some(Err(err)) => errors.push(err),
            Some(Ok(token)) => return Some(token),
            None => return None,
        }
    });
    let mut parser = parser::Parser::new(tokens);
    let Some(statements) = parser.parse().errors_into(&mut errors) else {
        return Err(errors);
    };
    let mut resolver = resolver::Resolver::new(interpreter);
    let Some(()) = resolver.resolve(&statements).error_into(&mut errors) else {
        return Err(errors);
    };
    let Some(()) = interpreter.interpret(&statements).error_into(&mut errors) else {
        return Err(errors);
    };
    errors.empty_ok(())
}

fn eval_with(source: String, interpreter: &mut Interpreter) -> Result<Value, Errors<Error>> {
    let mut errors = Errors::new();
    let mut raw_tokens = Tokens::from(&*source);
    let tokens = iter::from_fn(|| loop {
        match raw_tokens.next() {
            Some(Err(err)) => errors.push(err),
            Some(Ok(token)) => return Some(token),
            None => return None,
        }
    });
    let mut parser = parser::Parser::new(tokens);
    let Some(expression) = parser.expression().error_into(&mut errors) else {
        return Err(errors);
    };
    let mut resolver = resolver::Resolver::new(interpreter);
    let Some(()) = resolver.expression(&expression).error_into(&mut errors) else {
        return Err(errors);
    };
    let Some(value) = interpreter
        .evaluate(&expression)
        .map_err(MaybeWithSignal::into_inner)
        .error_into(&mut errors)
    else {
        return Err(errors);
    };
    errors.empty_ok(value.into_owned())
}

fn run(source: String) -> Result<(), Errors<Error>> {
    run_with(source, &mut Interpreter::new())
}

#[derive(Parser)]
struct Args {
    /// Source file to read lox code from.
    file: Option<PathBuf>,

    /// Directly pass lox code inline to be interpreted.
    #[clap(short, long)]
    source: Option<String>,
}

fn _main() -> Result<(), RootError> {
    let args = Args::parse();

    match (args.file, args.source) {
        // run code inline
        (_, Some(source)) => {
            run(source)?;
        }

        // run from source file
        (Some(file), _) => {
            let source = std::fs::read_to_string(file)?;
            run(source)?;
        }

        // execute repl
        _ => {
            let mut interpreter = Interpreter::new();
            loop {
                print!("> ");
                stdout().flush()?;
                let Some(line) = stdin().lines().next() else {
                    // ctrl+D or ctrl+Z
                    break;
                };
                let line = line?;
                let result = if line.trim().ends_with(';') {
                    run_with(line, &mut interpreter)
                } else {
                    eval_with(line, &mut interpreter).map(|val| println!("{val}"))
                };
                match result {
                    Ok(_) => (),
                    Err(errs) => println!("{errs}"),
                }
            }
        }
    }

    Ok(())
}

// wish i didnt have to do this 😞
fn main() -> ExitCode {
    match _main() {
        Ok(_) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("{err}");
            err.report()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::run;

    #[test]
    fn resolver() {
        if let Err(errs) = run(r#"
var a = "global";
{
  fun showA() {
    print a;
  }

  showA();
  var a = "block";
  showA();
  print "a: " + a;
}"#
        .to_string())
        {
            eprintln!("{errs}");
        }
    }
}
