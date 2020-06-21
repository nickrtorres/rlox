use std::env;
use std::error;
use std::fs::read_to_string;
use std::io::{self, stdin, BufRead, Write};
use std::result;

use program::perror;

extern crate rlox;
use rlox::core::{Interpreter, Parser, Resolver, RloxError, Scanner};

type Error = Box<dyn error::Error>;
type Result<T> = result::Result<T, Error>;

fn run(buf: String, interpreter: &mut Interpreter) -> Result<()> {
    let scanner = Scanner::new(buf);
    let parser = Parser::new(scanner.scan_tokens());
    let mut statements = parser.parse_stmts()?;

    let mut resolver = Resolver::new();
    resolver.resolve(&mut statements)?;
    let locals = resolver.into_locals()?;
    interpreter.resolve(locals);
    interpreter.interpret(statements)?;

    Ok(())
}

fn run_prompt() -> Result<()> {
    let stdin = stdin();
    let mut interpreter = Interpreter::new();
    loop {
        print!("> ");
        io::stdout().flush()?;
        let mut buf = String::with_capacity(1024);
        stdin.lock().read_line(&mut buf)?;
        run(buf, &mut interpreter)?;
    }
}

fn run_file(f: Option<&String>) -> Result<()> {
    let file = read_to_string(f.ok_or(RloxError::Unreachable)?)?;

    let mut interpreter = Interpreter::new();
    run(file, &mut interpreter)?;
    Ok(())
}

fn fail_if_err(r: Result<()>) {
    if let Err(e) = r {
        perror(e)
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.len() {
        1 => fail_if_err(run_prompt()),
        2 => fail_if_err(run_file(args.get(1))),
        _ => perror("usage: rlox [script]".to_owned()),
    }
}
