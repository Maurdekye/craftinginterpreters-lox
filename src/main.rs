use std::{
    io::{stdin, stdout, Write},
    path::PathBuf,
};

use thiserror::Error;

use clap::Parser;

mod lexer;

#[derive(Clone, Debug, Error)]
enum Error {
    
}

fn run(source: String) -> Result<(), Error> {
    println!("'{source}'");
    Ok(())
}

#[derive(Parser)]
struct Args {
    file: Option<PathBuf>,

    #[clap(short, long)]
    source: Option<String>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    match (args.file, args.source) {
        (_, Some(source)) => run(source)?,
        (Some(file), _) => {
            let source = std::fs::read_to_string(file)?;
            run(source)?;
        }
        _ => loop {
            print!("> ");
            stdout().flush()?;
            let Some(maybe_line) = stdin().lines().next() else {
                break;
            };
            let line = maybe_line?;
            run(line)?;
        },
    }

    Ok(())
}
