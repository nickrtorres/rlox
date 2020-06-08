use std::error;
use std::fs::File;
use std::io::Read;
use std::process::Command;
use std::result;

type Error = Box<dyn error::Error>;
type Result<T> = result::Result<T, Error>;

/// Gets the correct stdout file given the category and test
fn expected_output(category: &str, test: &str) -> Result<Vec<u8>> {
    let mut f = File::open(format!("tests/output/{}/{}.stdout", category, test))?;

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

macro_rules! verify_rlox_program {
    ($category:expr, $test: expr) => {
        paste::item! {
            #[test]
            fn [<lox_ $category _ $test>]() -> Result<()> {
                let actual = cmd($category, $test)?;
                let expected = expected_output($category, $test)?;

                assert_eq!(actual, expected);
                Ok(())
            }
        }
    };
}

// Assignment
verify_rlox_program! {"assignment", "associativity"}
verify_rlox_program! {"assignment", "global"}
verify_rlox_program! {"assignment", "syntax"}

// Functions
verify_rlox_program! {"function", "empty_body"}
verify_rlox_program! {"function", "local_recursion"}
verify_rlox_program! {"function", "mutual_recursion"}
verify_rlox_program! {"function", "parameters"}
verify_rlox_program! {"function", "print"}
verify_rlox_program! {"function", "recursion"}
