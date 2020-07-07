use super::{Expr, FunctionStmt, LoxCallable, Result, RloxError, Stmt, Token, INIT_METHOD};

use std::collections::HashMap;

type Stack<T> = Vec<T>;

#[derive(Debug, Clone, Copy)]
enum FunctionType {
    Function,
    Method,
    Initializer,
}

#[derive(Clone, Copy)]
struct ClassType;

pub struct Resolver {
    scopes: Stack<HashMap<String, bool>>,
    locals: HashMap<Expr, usize>,
    current_function: Option<FunctionType>,
    current_class: Option<ClassType>,
}

impl Resolver {
    pub fn new() -> Self {
        Resolver {
            scopes: Stack::new(),
            locals: HashMap::new(),
            current_function: None,
            current_class: None,
        }
    }

    pub fn resolve(&mut self, statements: &[Stmt]) -> Result<()> {
        for statement in statements {
            self.resolve_statment(statement)?;
        }

        Ok(())
    }

    pub fn into_locals(self) -> HashMap<Expr, usize> {
        self.locals
    }

    fn resolve_statment(&mut self, statement: &Stmt) -> Result<()> {
        match statement {
            Stmt::Block(statements) => {
                self.begin_scope();
                self.resolve(statements)?;
                self.end_scope();
            }
            Stmt::Class(name, methods) => {
                let enclosing = self.current_class;
                self.current_class = Some(ClassType);
                self.declare(name)?;
                self.define(name);

                self.begin_scope();
                self.scopes
                    .last_mut()
                    .map(|m| m.insert("this".to_owned(), true));
                for method in methods {
                    if let Stmt::Function(LoxCallable::UserDefined(f)) = method {
                        if f.name.lexeme == INIT_METHOD.to_owned() {
                            self.resolve_function(f, Some(FunctionType::Initializer))?;
                        } else {
                            self.resolve_function(f, Some(FunctionType::Method))?;
                        }
                    } else {
                        unreachable!();
                    }
                }

                self.end_scope();
                self.current_class = enclosing;
            }
            Stmt::If(expr, then_branch, else_branch) => {
                self.resolve_expression(expr)?;
                self.resolve_statment(then_branch)?;
                if let Some(e) = else_branch {
                    self.resolve_statment(e)?;
                }
            }
            Stmt::Expression(expr) | Stmt::Print(expr) => {
                self.resolve_expression(&expr)?;
            }
            Stmt::Return(_, Some(expr)) => {
                if self.current_function.is_none() {
                    return Err(RloxError::ReturnInNonFunction);
                } else if let Some(FunctionType::Initializer) = self.current_function {
                    return Err(RloxError::ReturnValueFromConstructor);
                } else {
                    self.resolve_expression(&expr)?;
                }
            }
            Stmt::Var(name, initializer) => {
                self.declare(name)?;

                if let Some(initializer) = initializer {
                    self.resolve_expression(initializer)?;
                }

                self.define(name)
            }
            Stmt::While(condition, body) => {
                self.resolve_expression(condition)?;
                self.resolve_statment(body)?;
            }
            Stmt::Function(f) => {
                let func = match f {
                    LoxCallable::UserDefined(s) => s,
                    _ => unreachable!(),
                };

                self.declare(&func.name)?;
                self.define(&func.name);

                self.resolve_function(func, Some(FunctionType::Function))?;
            }
            _ => {}
        }

        Ok(())
    }

    fn resolve_expression(&mut self, expr: &Expr) -> Result<()> {
        match expr {
            Expr::Assign(token, expr) => {
                self.resolve_expression(expr)?;
                self.resolve_local(expr, token)?;
            }
            Expr::Literal(_) => {}
            Expr::Binary(left, _, right) | Expr::Logical(left, _, right) => {
                self.resolve_expression(left)?;
                self.resolve_expression(right)?;
            }
            Expr::Unary(_, expr) | Expr::Grouping(expr) => {
                self.resolve_expression(expr)?;
            }
            Expr::Variable(token) => {
                if !self.scopes.is_empty() {
                    if let Some(false) = self.scopes.last().and_then(|m| m.get(&token.lexeme)) {
                        // TODO 11.3.3 "Cannot read local variable in its own initializer."
                        // I'm not sure if this is a possible state or not
                        unimplemented!()
                    }
                }

                self.resolve_local(expr, token)?;
            }
            Expr::Call(callee, _, args) => {
                self.resolve_expression(callee)?;

                for arg in args {
                    self.resolve_expression(arg)?;
                }
            }
            Expr::Get(object, _) => self.resolve_expression(object)?,
            Expr::Set(object, _, value) => {
                self.resolve_expression(object)?;
                self.resolve_expression(value)?;
            }
            Expr::This(token) => {
                if self.current_class.is_none() {
                    return Err(RloxError::ThisOutsideOfClass);
                }

                self.resolve_local(expr, token)?;
            }
        }

        Ok(())
    }

    fn resolve_local(&mut self, expr: &Expr, name: &Token) -> Result<()> {
        for (i, scope) in self.scopes.iter().enumerate() {
            if scope.contains_key(&name.lexeme) {
                // Crafting Interpreters 11.3.3:
                // > "If we find the variable, we tell the interpreter it has been
                //   resolved, passing in the number of scopes between the
                //   current innermost scope and the scope where the variable
                //   was found. So, if the variable was found in the current
                //   scope, it passes in 0. If it’s in the immediately enclosing
                //   scope, 1. You get the idea."
                self.locals.insert(expr.clone(), self.scopes.len() - 1 - i);
            }
        }

        Ok(())
    }

    fn resolve_function(
        &mut self,
        function: &FunctionStmt,
        function_type: Option<FunctionType>,
    ) -> Result<()> {
        let enclosing = self.current_function;
        self.current_function = function_type;

        self.begin_scope();

        for param in function.parameters.iter() {
            self.declare(param)?;
            self.define(param);
        }

        self.resolve(&function.body)?;
        self.end_scope();
        self.current_function = enclosing;

        Ok(())
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn declare(&mut self, name: &Token) -> Result<()> {
        if self
            .scopes
            .last()
            .map_or(false, |m| m.contains_key(&name.lexeme))
        {
            return Err(RloxError::VariableRedefinition);
        }

        self.scopes
            .last_mut()
            .map(|m| m.insert(name.lexeme.clone(), false));

        Ok(())
    }

    fn define(&mut self, name: &Token) {
        self.scopes
            .last_mut()
            .map(|m| m.entry(name.lexeme.clone()).insert(true));
    }
}
