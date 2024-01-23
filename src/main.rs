use std::{
    fmt::Display,
    io::{stdin, stdout, Write},
    path::PathBuf,
    error::Error as StdError,
};

use lexer::Tokens;
use thiserror::Error as ThisError;

use clap::Parser;

use crate::lexer::TokenLocation;

mod lexer;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Error from lexer: {0}")]
    Lexer(#[from] lexer::Error),
}

#[derive(Clone, Debug)]
pub struct Errors<E>(pub Vec<E>);

impl<E> Errors<E> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push<T: Into<E>>(&mut self, error: T) {
        self.0.push(error.into());
    }

    /// If there are no errors, return an Ok with the passed value
    pub fn empty_ok<T>(self, ok: T) -> Result<T, Self> {
        self.0.is_empty().then_some(ok).ok_or(self)
    }
}

impl<E: Display> Display for Errors<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for err in &self.0 {
            writeln!(f, "{err}")?;
        }
        Ok(())
    }
}

impl<E: StdError> StdError for Errors<E> {}

fn run(source: String) -> Result<(), Errors<Error>> {
    let mut errors = Errors::new();

    for token in Tokens::from(&*source) {
        match token {
            Ok(TokenLocation { token, .. }) => print!("{} ", token),
            Err(err) => errors.push(err),
        }
    }
    println!();

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
