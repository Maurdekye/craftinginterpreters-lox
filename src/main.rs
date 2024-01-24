use std::{
    error::Error as StdError,
    fmt::Display,
    io::{stdin, stdout, Write},
    iter,
    path::PathBuf,
};

use lexer::Tokens;
use parser::MaybeLocated;
use thiserror::Error as ThisError;

use clap::Parser;

mod lexer;
mod parser;
mod util;

#[derive(Clone, Debug, ThisError)]
pub enum Error {
    #[error("Lexer error: {0}")]
    Lexer(#[from] Located<lexer::Error>),
    #[error("Parser error: {0}")]
    Parser(#[from] MaybeLocated<parser::Error>),
}

#[derive(Clone, Debug)]
pub struct Located<T> {
    line: usize,
    character: usize,
    item: T,
}

impl<T: Display> Display for Located<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}:{}] {}", self.line, self.character, self.item)
    }
}

impl<T: StdError> StdError for Located<T> {}

pub trait Locateable {
    fn line(&self) -> usize;
    fn character(&self) -> usize;
}

impl<T> Locateable for Located<T> {
    fn line(&self) -> usize {
        self.line
    }

    fn character(&self) -> usize {
        self.character
    }
}

pub trait LocatedAt<T: Locateable>: Sized {
    fn at(self, locator: &T) -> Located<Self> {
        Located {
            line: locator.line(),
            character: locator.character(),
            item: self,
        }
    }
}

impl<L: Locateable, T> LocatedAt<L> for T {}

#[derive(Clone, Debug)]
pub struct Errors<E>(Vec<E>);

impl<E> Errors<E> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, error: impl Into<E>) {
        self.0.push(error.into());
    }

    /// If there are no errors, return an Ok with the passed value
    pub fn empty_ok<T>(self, ok: T) -> Result<T, Self> {
        self.0.is_empty().then_some(ok).ok_or(self)
    }

    pub fn map<F, O>(self, f: F) -> Errors<O>
    where
        F: FnMut(E) -> O,
    {
        Errors(self.0.into_iter().map(f).collect())
    }
}

impl<E> From<Vec<E>> for Errors<E> {
    fn from(value: Vec<E>) -> Self {
        Errors(value)
    }
}

impl<E> FromIterator<E> for Errors<E> {
    fn from_iter<T: IntoIterator<Item = E>>(iter: T) -> Self {
        Errors(iter.into_iter().collect())
    }
}

// doesnt work :(
// impl<E, O: From<E>> From<Errors<E>> for Errors<O> {
//     fn from(value: Errors<E>) -> Self {
//         value.map(From::from)
//     }
// }

impl<E: Display> Display for Errors<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for err in &self.0 {
            writeln!(f, "{err}")?;
        }
        Ok(())
    }
}

impl<E, T: Default> Into<Result<T, Errors<E>>> for Errors<E> {
    fn into(self) -> Result<T, Errors<E>> {
        self.empty_ok(T::default())
    }
}

impl<E: StdError> StdError for Errors<E> {}

/// Interpret lox code, evaluating and printing the execution result,
/// and then return a list of any errors that may have been encountered
fn run(source: String) -> Result<(), Errors<Error>> {
    let mut dirty_tokens = Tokens::from(&*source);
    let clean_tokens = iter::from_fn(|| loop {
        match dirty_tokens.next() {
            Some(Err(err)) => println!("{err}"),
            Some(Ok(token)) => return Some(token),
            None => return None,
        }
    });
    let source = parser::parse(clean_tokens).map_err(|e| e.map(Error::from))?;
    println!("{source}");
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
