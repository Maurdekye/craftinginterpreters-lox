use std::{
    io::{stdin, stdout, Write},
    path::PathBuf,
};

use lexer::Tokens;
use thiserror::Error;

use clap::Parser;

use crate::lexer::TokenLocation;

mod lexer;

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("Error from lexer: {0}")]
    Lexer(#[from] lexer::Error),
}

fn run(source: String) -> Result<(), Error> {
    let mut errors = Vec::new();

    for token in Tokens::from(&*source) {
        match token {
            Ok(TokenLocation { token, .. }) => print!("{} ", token),
            Err(err) => errors.push(err),
        }
    }
    println!();

    if !errors.is_empty() {
        println!("{} errors:", errors.len());
        for error in errors {
            println!("{}", error);
        }
    }

    Ok(())
}

#[derive(Parser)]
struct Args {
    /// Source file to read lox code from.
    file: Option<PathBuf>,

    /// Directly pass lox code inline to be interpreted.
    #[clap(short, long)]
    source: Option<String>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
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
