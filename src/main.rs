use std::{
    error::Error as StdError,
    io::{stdin, stdout, Write},
    iter,
    path::PathBuf,
};

use lexer::Tokens;
use thiserror::Error as ThisError;

use clap::Parser;
use util::{Errors, Located, MaybeLocated};

use crate::util::ErrorsInto;

mod interpreter;
mod lexer;
mod parser;
mod util;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Lexer error: {0}")]
    Lexer(#[from] Located<lexer::Error>),
    #[error("Parser error:\n{0}")]
    Parser(#[from] MaybeLocated<parser::Error>),
    #[error("Interpreter error:\n{0}")]
    Interpreter(#[from] MaybeLocated<interpreter::Error>),
}

impl From<Errors<MaybeLocated<parser::Error>>> for Errors<Error> {
    fn from(value: Errors<MaybeLocated<parser::Error>>) -> Self {
        value.map(From::from)
    }
}

/// Interpret lox code, evaluating and printing the execution result,
/// and then return a list of any errors that may have been encountered
fn run(source: String) -> Result<(), Errors<Error>> {
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
    let Some(result) = interpreter::interpret(expression).errors_into(&mut errors) else {
        return Err(errors);
    };
    println!("{result}");
    errors.empty_ok(())
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
        (_, Some(source)) => run(source)?,

        // run from source file
        (Some(file), _) => {
            let source = std::fs::read_to_string(file)?;
            run(source)?;
        }

        // execute repl
        _ => loop {
            print!("> ");
            stdout().flush()?;
            let Some(line) = stdin().lines().next() else {
                // ctrl+D or ctrl+Z
                break;
            };
            if let Err(err) = run(line?) {
                // error interpreting code
                println!("{err}");
            }
        },
    }

    Ok(())
}
