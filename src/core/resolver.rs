use super::{Expr, FunctionStmt, LoxCallable, Result, RloxError, Stmt, Token};

use std::collections::HashMap;
use std::rc::Rc;

type Stack<T> = Vec<T>;

#[derive(Debug, Clone, Copy)]
struct Function;
type FunctionType = Option<Function>;

pub struct Resolver {
    scopes: Stack<HashMap<Rc<str>, bool>>,
    locals: HashMap<Expr, usize>,
    current_function: FunctionType,
}

impl Resolver {
    pub fn new() -> Self {
        Resolver {
            scopes: Stack::new(),
            locals: HashMap::new(),
            current_function: None,
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
                }

                self.resolve_expression(&expr)?;
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
                    _ => return Err(RloxError::Unreachable),
                };

                self.declare(&func.name)?;
                self.define(&func.name);

                self.resolve_function(func, Some(Function {}))?;
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
                    if let Some(false) = self.scopes.last().map(|m| m.get(&token.lexeme)).flatten()
                    {
                        // TODO 11.3.3 "Cannot read local variable in its own initializer."
                        return Err(RloxError::Unreachable);
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
        function_type: FunctionType,
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
            .map(|m| m.insert(Rc::clone(&name.lexeme), false));

        Ok(())
    }

    fn define(&mut self, name: &Token) {
        self.scopes
            .last_mut()
            .map(|m| m.entry(Rc::clone(&name.lexeme)).insert(true));
    }
}
