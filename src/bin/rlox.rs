use program::perror;
use std::env;
use std::error;
use std::fs::File;
use std::io::{self, stdin, BufRead, BufReader, Write};
use std::result;

type Error = Box<dyn error::Error>;
type Result<T> = result::Result<T, Error>;

fn run<T: BufRead>(b: &mut T) -> Result<()> {
    let mut buf = String::with_capacity(1024);
    let _ = b.read_line(&mut buf)?;
    for token in buf.split_whitespace() {
        println!("{}", token);
    }

    Ok(())
}

fn run_prompt() -> Result<()> {
    let stdin = stdin();
    loop {
        print!("> ");
        io::stdout().flush()?;
        run(&mut stdin.lock())?;
    }
}

fn run_file(f: &str) -> Result<()> {
    let file = File::open(f).map_err(|e| format!("{}: {}", f, e))?;
    run(&mut BufReader::new(file))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() > 2 {
        perror(format!("usage: rlox [script]"));
    } else if args.len() == 2 {
        if let Err(e) = run_file(&args[1]) {
            perror(e);
        }
    } else {
        if let Err(e) = run_prompt() {
            perror(e);
        }
    }
}
