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

mod lexer;
mod parser;
mod util;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Lexer error: {0}")]
    Lexer(#[from] Located<lexer::Error>),
    #[error("Parser error:\n{0}")]
    Parser(#[from] MaybeLocated<parser::Error>),
}

/// Interpret lox code, evaluating and printing the execution result,
/// and then return a list of any errors that may have been encountered
fn run(source: String) -> Result<(), Errors<Error>> {
    let mut errors = Errors::new();
    let mut tokens = Tokens::from(&*source);
    let source = match parser::parse(iter::from_fn(|| loop {
        match tokens.next() {
            Some(Err(err)) => errors.push(err),
            Some(Ok(token)) => return Some(token),
            None => return None,
        }
    })) {
        Ok(source) => source,
        Err(errs) => {
            errors.extend(errs);
            return Err(errors);
        }
    };
    println!("{source}");
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
    // let args = Args::parse_from(["_", "test.lox"]);

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
