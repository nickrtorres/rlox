//! `librlox` is the library that powers the rlox interpreter.
//!
//! `rlox` is a rust port of the Lox Java interpreter (i.e. `jlox`).  `rlox`
//! differs from `jlox` is a number of ways namely:
//! - `rlox` uses `std::result::Result` to report errors (`jlox` uses exceptions)
//! - `rlox` uses `Expr` and `Stmt` sum types to represent expressions and
//!   statements, respectively (`jlox` uses abstract `Expr` and `Stmt` classes and
//!   specialized subclasses).
//! - `rlox` defines associated functions for `Expr` and `Stmt` to operate on
//!   variants of each type (`jlox` uses the visitor pattern)
//! - `rlox` defines an `interpret` associated function directly on the `Expr`
//!   type (`jlox` uses a new `Interpreter` object with an `interpret` method
#![feature(bool_to_option)]
#![feature(entry_insert)]
#![warn(clippy::pedantic)]

pub mod core;
