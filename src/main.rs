use std::{
    error::Error as StdError,
    io::{stdin, stdout, Write},
    iter,
    path::PathBuf,
};

use interpreter::Value;
use lexer::Tokens;
use thiserror::Error as ThisError;

use clap::Parser;
use util::{Errors, Located, MaybeLocated};

use crate::{interpreter::Interpreter, util::ErrorsInto};

mod interpreter;
mod lexer;
mod parser;
mod util;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Lexer: {0}")]
    Lexer(#[from] Located<lexer::Error>),
    #[error("Parser:\n{0}")]
    Parser(#[from] MaybeLocated<parser::Error>),
    #[error("Interpreter:\n{0}")]
    Interpreter(#[from] Located<interpreter::Error>),
}

impl From<Errors<MaybeLocated<parser::Error>>> for Errors<Error> {
    fn from(value: Errors<MaybeLocated<parser::Error>>) -> Self {
        value.map(From::from)
    }
}

/// Interpret lox code, evaluating and printing the execution result,
/// and then return a list of any errors that may have been encountered
fn run_with(source: String, interpreter: &mut Interpreter) -> Result<Value, Errors<Error>> {
    let mut errors: Errors<Error> = Errors::new();
    let mut raw_tokens = Tokens::from(&*source);
    let tokens = iter::from_fn(|| loop {
        match raw_tokens.next() {
            Some(Err(err)) => errors.push(err),
            Some(Ok(token)) => return Some(token),
            None => return None,
        }
    });
    let Some(expression) = parser::parse(tokens).errors_into(&mut errors) else {
        return Err(errors);
    };
    let Some(result) = interpreter.interpret(expression).errors_into(&mut errors) else {
        return Err(errors);
    };
    errors.empty_ok(result)
}

fn run(source: String) -> Result<Value, Errors<Error>> {
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

fn main() -> Result<(), Box<dyn StdError>> {
    let args = Args::parse();

    match (args.file, args.source) {
        // run code inline
        (_, Some(source)) => println!("{}", run(source)?),

        // run from source file
        (Some(file), _) => {
            let source = std::fs::read_to_string(file)?;
            println!("{}", run(source)?);
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
                match run_with(line?, &mut interpreter) {
                    Ok(value) => println!("{value}"),
                    Err(errs) => println!("{errs}"),
                }
            }
        }
    }

    Ok(())
}
