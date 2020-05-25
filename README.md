# rlox

`rlox` is a work-in-progress port of jlox, a tree walk interpreter written in
Java. There are a number of incomplete features in this repository. An
incomplete list is provided below.

### Sections from [Crafting Interpreters]
- [x] Scanning
- [x] Representing Code
- [x] Parsing Expressions
- [x] Evaluating Expressions
- [x] Statements and State
- [x] Control Flow
- [ ] Functions
- [ ] Resolving and Binding
- [ ] Classes
- [ ] Inheritance

### General
- [ ] Error handling
- [ ] Documentation
- [ ] Tests
- [ ] Modules


## Building
`rlox` requires nightly for `#![feature(str_strip)]` and `#![feature(bool_to_option)]`
```
$ rustup default nightly
$ rustup update
$ cargo test
```

[Crafting Interpreters]: https://craftinginterpreters.com/contents.html
