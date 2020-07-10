use std::error;
use std::fs::File;
use std::io::Read;
use std::process::{Command, Output};
use std::result;

type Error = Box<dyn error::Error>;
type Result<T> = result::Result<T, Error>;

enum FileType {
    Stdout,
    Stderr,
}

fn get_file(file_type: FileType, category: &str, test: &str) -> Result<File> {
    let mut path = format!("tests/output/{}/{}.", category, test);

    match file_type {
        FileType::Stdout => path.push_str("stdout"),
        FileType::Stderr => path.push_str("stderr"),
    }

    let file = File::open(path)?;
    Ok(file)
}

/// Gets the correct stdout file given the category and test
fn expected_output(mut file: File) -> Result<Vec<u8>> {
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    Ok(buffer)
}

fn cmd(category: &str, test: &str) -> Result<Output> {
    let output = Command::new("./target/debug/rlox")
        .arg(format!("tests/lox/{}/{}.lox", category, test))
        .output()?;
    Ok(output)
}

macro_rules! verify_rlox_program_ok {
    ($category:expr, $test: expr) => {
        paste::item! {
            #[test]
            fn [<lox_ $category _ $test>]() -> Result<()> {
                let actual = cmd($category, $test)?;
                let expected = expected_output(get_file(FileType::Stdout, $category, $test)?)?;

                assert_eq!(actual.stdout, expected);
                Ok(())
            }
        }
    };
}

macro_rules! verify_rlox_program_err {
    ($category:expr, $test: expr) => {
        paste::item! {
            #[test]
            fn [<lox_ $category _ $test>]() -> Result<()> {
                let actual = cmd($category, $test)?;
                let expected = expected_output(get_file(FileType::Stderr, $category, $test)?)?;

                assert_eq!(actual.stderr, expected);
                Ok(())
            }
        }
    };
}

// Assignment (ok)
verify_rlox_program_ok! {"assignment", "associativity"}
verify_rlox_program_ok! {"assignment", "global"}
verify_rlox_program_ok! {"assignment", "syntax"}

// Constructor (ok)
verify_rlox_program_ok! {"constructor", "arguments"}
verify_rlox_program_ok! {"constructor", "call_init_early_return"}
verify_rlox_program_ok! {"constructor", "call_init_explicitly"}
verify_rlox_program_ok! {"constructor", "default"}
verify_rlox_program_ok! {"constructor", "early_return"}
verify_rlox_program_ok! {"constructor", "init_not_method"}
verify_rlox_program_ok! {"constructor", "return_in_nested_function"}

// Constructor (err)
verify_rlox_program_err! {"constructor", "default_arguments"}
verify_rlox_program_err! {"constructor", "extra_arguments"}
verify_rlox_program_err! {"constructor", "missing_arguments"}
verify_rlox_program_err! {"constructor", "return_value"}

// Field (ok)
verify_rlox_program_ok! {"field", "many"}
verify_rlox_program_ok! {"field", "on_instance"}

// Function (ok)
verify_rlox_program_ok! {"function", "empty_body"}
verify_rlox_program_ok! {"function", "local_recursion"}
verify_rlox_program_ok! {"function", "mutual_recursion"}
verify_rlox_program_ok! {"function", "parameters"}
verify_rlox_program_ok! {"function", "print"}
verify_rlox_program_ok! {"function", "recursion"}

// Inheritance (ok)
verify_rlox_program_ok! {"inheritance", "constructor"}
verify_rlox_program_ok! {"inheritance", "inherit_methods"}

// Method (ok)
verify_rlox_program_ok! {"method", "arity"}
verify_rlox_program_ok! {"method", "empty_block"}

// Super (ok)
verify_rlox_program_ok! {"super", "call_other_method"}
verify_rlox_program_ok! {"super", "call_same_method"}
verify_rlox_program_ok! {"super", "constructor"}
verify_rlox_program_ok! {"super", "indirectly_inherited"}

// This (ok)
verify_rlox_program_ok! {"this", "this_in_method"}

// This (err)
verify_rlox_program_err! {"this", "this_at_top_level"}
verify_rlox_program_err! {"this", "this_in_top_level_function"}

// Variable (ok)
verify_rlox_program_ok! {"variable", "early_bound"}
verify_rlox_program_ok! {"variable", "in_middle_of_block"}
verify_rlox_program_ok! {"variable", "in_nested_block"}

// Variable (err)
verify_rlox_program_err! {"variable", "collide_with_parameter"}
verify_rlox_program_err! {"variable", "duplicate_local"}
verify_rlox_program_err! {"variable", "duplicate_parameter"}

// Return (err)
verify_rlox_program_err! {"return", "at_top_level"}
