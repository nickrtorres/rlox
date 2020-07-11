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

// Block (ok)
verify_rlox_program_ok! {"block", "empty"}
verify_rlox_program_ok! {"block", "scope"}

// Bool (ok)
verify_rlox_program_ok! {"bool", "not"}
verify_rlox_program_ok! {"bool", "equality"}

// Call (err)
verify_rlox_program_err! {"call", "bool"}
verify_rlox_program_err! {"call", "nil"}
verify_rlox_program_err! {"call", "num"}
verify_rlox_program_err! {"call", "object"}
verify_rlox_program_err! {"call", "string"}

// Class (ok)
verify_rlox_program_ok! {"class", "empty"}

// Comments (ok)
verify_rlox_program_ok! {"comments", "line_at_eof"}
verify_rlox_program_ok! {"comments", "only_line_comment"}
verify_rlox_program_ok! {"comments", "only_line_comment_and_line"}
verify_rlox_program_ok! {"comments", "unicode"}

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
verify_rlox_program_ok! {"field", "call_function_field"}
verify_rlox_program_ok! {"field", "get_and_set_method"}
verify_rlox_program_ok! {"field", "many"}
verify_rlox_program_ok! {"field", "method"}
verify_rlox_program_ok! {"field", "method_binds_this"}
verify_rlox_program_ok! {"field", "on_instance"}

// Field (err)
verify_rlox_program_err! {"field", "call_nonfunction_field"}
verify_rlox_program_err! {"field", "get_on_bool"}
verify_rlox_program_err! {"field", "get_on_class"}
verify_rlox_program_err! {"field", "get_on_function"}
verify_rlox_program_err! {"field", "get_on_nil"}
verify_rlox_program_err! {"field", "get_on_num"}
verify_rlox_program_err! {"field", "get_on_string"}
verify_rlox_program_err! {"field", "set_on_bool"}
verify_rlox_program_err! {"field", "set_on_class"}
verify_rlox_program_err! {"field", "set_on_function"}
verify_rlox_program_err! {"field", "set_on_nil"}
verify_rlox_program_err! {"field", "set_on_num"}
verify_rlox_program_err! {"field", "set_on_string"}
verify_rlox_program_err! {"field", "undefined"}

// Function (ok)
verify_rlox_program_ok! {"function", "empty_body"}
verify_rlox_program_ok! {"function", "local_recursion"}
verify_rlox_program_ok! {"function", "mutual_recursion"}
verify_rlox_program_ok! {"function", "parameters"}
verify_rlox_program_ok! {"function", "print"}
verify_rlox_program_ok! {"function", "recursion"}

// Function (err)
verify_rlox_program_err! {"function", "extra_arguments"}
verify_rlox_program_err! {"function", "missing_arguments"}
verify_rlox_program_err! {"function", "too_many_arguments"}
verify_rlox_program_err! {"function", "too_many_parameters"}

// If (ok)
verify_rlox_program_ok! {"if", "dangling_else"}
verify_rlox_program_ok! {"if", "else"}
verify_rlox_program_ok! {"if", "if"}

// Inheritance (ok)
verify_rlox_program_ok! {"inheritance", "constructor"}
verify_rlox_program_ok! {"inheritance", "inherit_methods"}

// Logical operator (ok)
verify_rlox_program_ok! {"logical_operator", "and"}

// Method (ok)
verify_rlox_program_ok! {"method", "arity"}
verify_rlox_program_ok! {"method", "empty_block"}

// Method (err)
verify_rlox_program_err! {"method", "extra_arguments"}
verify_rlox_program_err! {"method", "missing_arguments"}
verify_rlox_program_err! {"method", "not_found"}
verify_rlox_program_err! {"method", "too_many_arguments"}
verify_rlox_program_err! {"method", "too_many_parameters"}

// Nil (ok)
verify_rlox_program_ok! {"nil", "literal"}

// Return (err)
verify_rlox_program_err! {"return", "at_top_level"}

// String (ok)
verify_rlox_program_ok! {"string", "literals"}
verify_rlox_program_ok! {"string", "multiline"}

// String (err)
verify_rlox_program_err! {"string", "error_after_multiline"}
verify_rlox_program_err! {"string", "unterminated"}

// Super (ok)
verify_rlox_program_ok! {"super", "bound_method"}
verify_rlox_program_ok! {"super", "call_other_method"}
verify_rlox_program_ok! {"super", "call_same_method"}
verify_rlox_program_ok! {"super", "constructor"}
verify_rlox_program_ok! {"super", "indirectly_inherited"}
verify_rlox_program_ok! {"super", "reassign_superclass"}

// Super (err)
verify_rlox_program_err! {"super", "extra_arguments"}
verify_rlox_program_err! {"super", "missing_arguments"}
verify_rlox_program_err! {"super", "no_superclass_bind"}
verify_rlox_program_err! {"super", "no_superclass_method"}
verify_rlox_program_err! {"super", "parenthesized"}
verify_rlox_program_err! {"super", "super_at_top_level"}
verify_rlox_program_err! {"super", "super_in_top_level_function"}
verify_rlox_program_err! {"super", "super_without_dot"}
verify_rlox_program_err! {"super", "super_without_name"}
verify_rlox_program_err! {"super", "no_superclass_call"}

// This (ok)
verify_rlox_program_ok! {"this", "this_in_method"}

// This (err)
verify_rlox_program_err! {"this", "this_at_top_level"}
verify_rlox_program_err! {"this", "this_in_top_level_function"}

// Variable (ok)
verify_rlox_program_ok! {"variable", "early_bound"}
verify_rlox_program_ok! {"variable", "in_middle_of_block"}
verify_rlox_program_ok! {"variable", "in_nested_block"}
verify_rlox_program_ok! {"variable", "local_from_method"}
verify_rlox_program_ok! {"variable", "redeclare_global"}
verify_rlox_program_ok! {"variable", "redefine_global"}
verify_rlox_program_ok! {"variable", "scope_reuse_in_different_blocks"}
verify_rlox_program_ok! {"variable", "shadow_and_local"}
verify_rlox_program_ok! {"variable", "shadow_global"}
verify_rlox_program_ok! {"variable", "shadow_local"}
verify_rlox_program_ok! {"variable", "uninitialized"}
verify_rlox_program_ok! {"variable", "unreached_undefined"}
verify_rlox_program_ok! {"variable", "use_global_in_initializer"}

// Variable (err)
verify_rlox_program_err! {"variable", "collide_with_parameter"}
verify_rlox_program_err! {"variable", "duplicate_local"}
verify_rlox_program_err! {"variable", "duplicate_parameter"}
verify_rlox_program_err! {"variable", "undefined_local"}
verify_rlox_program_err! {"variable", "use_false_as_var"}
verify_rlox_program_err! {"variable", "use_nil_as_var"}
verify_rlox_program_err! {"variable", "use_this_as_var"}
verify_rlox_program_err! {"variable", "undefined_global"}

// While (ok)
verify_rlox_program_ok! {"while", "return_inside"}
verify_rlox_program_ok! {"while", "syntax"}

// While (err)
verify_rlox_program_err! {"while", "class_in_body"}
verify_rlox_program_err! {"while", "fun_in_body"}
verify_rlox_program_err! {"while", "var_in_body"}
