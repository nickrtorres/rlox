extern crate rlox;
use rlox::{Interpreter, Parser, Scanner};

use program::perror;
use std::env;
use std::error;
use std::io::{self, stdin, BufRead, Write};
use std::result;

type Error = Box<dyn error::Error>;
type Result<T> = result::Result<T, Error>;

fn run<T: BufRead>(b: &mut T, interpreter: &mut Interpreter) -> Result<()> {
    let mut buf = String::with_capacity(1024);
    b.read_line(&mut buf)?;

    let scanner = Scanner::new(buf);
    let parser = Parser::new(scanner.scan_tokens());
    let statements = parser.parse_stmts()?;

    // for some reason return interpreter.interpret(statements) doesn't work ?
    interpreter.interpret(statements)?;

    Ok(())
}

fn run_prompt() -> Result<()> {
    let stdin = stdin();
    let mut interpreter = Interpreter::new();
    loop {
        print!("> ");
        io::stdout().flush()?;
        run(&mut stdin.lock(), &mut interpreter)?;
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.len() {
        x if x > 2 => perror("usage: rlox [script]".to_owned()),
        _ => {
            if let Err(e) = run_prompt() {
                perror(e);
            }
        }
    }
}
