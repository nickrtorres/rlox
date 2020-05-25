use std::error;
use std::fs::File;
use std::io::Read;
use std::process::Command;
use std::result;

type Error = Box<dyn error::Error>;
type Result<T> = result::Result<T, Error>;

/// Gets the correct stdout file given the category and test
fn expected_output(category: &str, test: &str) -> Result<Vec<u8>> {
    let output_base = "tests/output";
    let mut f = File::open(format!("{}/{}/{}.stdout", output_base, category, test))?;

    let mut buffer = Vec::new();
    f.read_to_end(&mut buffer)?;

    Ok(buffer)
}

fn cmd(category: &str, test: &str) -> Result<Vec<u8>> {
    let output = Command::new("./target/debug/rlox")
        .arg(format!("tests/lox/{}/{}.lox", category, test))
        .output()?;

    Ok(output.stdout)
}

#[test]
fn lox_assignment_associativity() -> Result<()> {
    let actual = cmd("assignment", "associativity")?;
    let expected = expected_output("assignment", "associativity")?;

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn lox_assignment_global() -> Result<()> {
    let actual = cmd("assignment", "global")?;
    let expected = expected_output("assignment", "global")?;

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn lox_assignment_syntax() -> Result<()> {
    let actual = cmd("assignment", "syntax")?;
    let expected = expected_output("assignment", "syntax")?;

    assert_eq!(actual, expected);
    Ok(())
}
