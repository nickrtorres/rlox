use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::mem;

use super::{Object, Result, RloxError, Walk};

/// A container for the interpreter's environment that can be arbitrarily nested.
#[derive(Debug, Clone)]
pub struct Environment {
    values: HashMap<String, Object>,
    enclosing: Option<Box<Environment>>,
}

impl Environment {
    /// Creates a new empty environment.
    #[must_use]
    pub fn new() -> Self {
        Environment {
            values: HashMap::new(),
            enclosing: None,
        }
    }

    /// Inserts `(name : value)` into self's environment
    pub fn define(&mut self, name: String, value: Object) {
        self.values.insert(name, value);
    }

    /// Returns the value of `name` in the first environment it's found in.
    ///
    /// # Returns
    /// Returns `Ok(Object)` in the first environment `name` is found in.
    /// Returns `Err(RloxError::UndefinedVariable(name))` if `name` is not found
    /// in any environment.
    pub fn get(&self, name: &str) -> Result<Object> {
        match self.values.get(name) {
            Some(s) => Ok(s.clone()),
            None => {
                if let Some(e) = &self.enclosing {
                    return e.get(name);
                }

                Err(RloxError::UndefinedVariable(name.to_owned()))
            }
        }
    }

    /// Assigns `value` in the first environment `name` is found in.
    pub fn assign(&mut self, name: &str, value: Object) -> Result<Object> {
        match self.values.entry(name.to_owned()) {
            Entry::Vacant(_) => {
                if let Some(e) = &mut self.enclosing {
                    return e.assign(name, value);
                }

                Err(RloxError::UndefinedVariable(name.to_owned()))
            }
            Entry::Occupied(mut e) => {
                e.insert(value);
                Ok(e.get().clone())
            }
        }
    }

    /// Raises an environment up a single level
    ///
    /// Given an arbitrary environment (`e`)
    /// ```notrust
    ///     +---------------+
    ///     | e             |
    ///     | =             |
    ///     | values: {     |
    ///     |   // ...      |
    ///     |   // ...      |
    ///     |   // ...      |
    ///     | }             |
    ///     |               |
    ///     | enclosing: ---+------> // ...
    ///     +---------------+       
    /// ```
    ///
    /// A call of `e.raise()` will raise the environment a single level:
    /// ```notrust
    ///
    ///     +-------------------------+
    ///     | ** New Environment **   |
    ///     | =====================   |
    ///     | values: HashMap::new(), |
    ///     | enclosing: -------------+----->+---------------+
    ///     +-------------------------+      | e             |
    ///                                      | =             |               
    ///                                      | values: {     |               
    ///                                      |   // ...      |               
    ///                                      |   // ...      |               
    ///                                      |   // ...      |               
    ///                                      | }             |               
    ///                                      |               |               
    ///                                      | enclosing: ---+------> // ...
    ///                                      +---------------+               
    ///                       
    ///                       
    /// ```
    ///
    /// # Note
    /// This is the inverse of `Environment::lower`.
    pub fn raise(&mut self) {
        self.enclosing = Some(Box::new(Environment {
            values: mem::replace(&mut self.values, HashMap::new()),
            enclosing: self.enclosing.take(),
        }));
    }

    /// Collapses the environment 1 level.
    ///
    /// Given an arbitrary environment (`e`) with a valid enclosing (`c`) environment:
    /// ```notrust
    ///     +---------------+
    ///     | e             |
    ///     | =             |
    ///     | values: {     |
    ///     |   // ...      |
    ///     |   // ...      |
    ///     |   // ...      |
    ///     | }             |
    ///     |               |
    ///     | enclosing: ---+------>+---------------+
    ///     +---------------+       | c             |
    ///                             | =             |
    ///                             | values: {     |
    ///                             |   // ...      |
    ///                             |   // ...      |
    ///                             |   // ...      |
    ///                             | }             |
    ///                             |               |
    ///                             | enclosing: ---+------> // ...
    ///                             +---------------+
    /// ```
    ///
    /// A call of `e.lower()` will collapse the environment:
    /// ```notrust
    ///     +---------------+
    ///     | c             |
    ///     | =             |
    ///     | values: {     |
    ///     |   // ...      |
    ///     |   // ...      |
    ///     |   // ...      |
    ///     | }             |
    ///     |               |
    ///     | enclosing: ---+------> // ...
    ///     +---------------+       
    /// ```
    ///
    /// # Panics
    /// `lower` is infallible. It is the responsibility of the programmer to
    /// ensure that the current environment has an enclosing environment and .
    /// Failure to meet the condition above will crash rlox.
    ///
    /// # Note
    /// This is the inverse of `Environment::raise`.
    pub fn lower(&mut self) {
        assert!(self.enclosing.is_some());
        let enclosing = self.enclosing.take().unwrap();

        *self = *enclosing;
    }

    /// Gets `name` in environment at `distance`
    ///
    /// Walks through the chain of `self`'s environment to distance and then searches for `name`.
    ///
    /// # Panics
    /// Panics if `distance` is unreachable.
    pub fn get_at(&self, distance: usize, name: &str) -> Result<Object> {
        for (i, env) in self.walker().enumerate() {
            if i == distance {
                return env.get(name);
            }
        }

        unreachable!(format!("distance: {} is unreachable!", distance));
    }

    fn walker(&self) -> EnvironmentWalker {
        EnvironmentWalker {
            current: Some(self),
        }
    }
}

struct EnvironmentWalker<'a> {
    current: Option<&'a Environment>,
}

impl<'a> Walk<'a> for EnvironmentWalker<'a> {
    type Item = &'a Environment;
    fn walk(&mut self) -> Option<Self::Item> {
        let data = self.current;
        self.current = self.current.and_then(|e| e.enclosing.as_deref());
        data
    }
}

impl<'a> Iterator for EnvironmentWalker<'a> {
    type Item = &'a Environment;

    fn next(&mut self) -> Option<Self::Item> {
        self.walk()
    }
}
