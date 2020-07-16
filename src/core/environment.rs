use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::iter::FromIterator;
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

        panic!(format!("distance: {} is unreachable!", distance));
    }

    fn walker(&self) -> EnvironmentWalker {
        EnvironmentWalker {
            current: Some(self),
        }
    }
}

/// Constructs an environment from an iterator.
impl FromIterator<(String, Object)> for Environment {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (String, Object)>,
    {
        let mut values = HashMap::new();
        values.extend(iter);

        Environment {
            values,
            enclosing: None,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_can_store_and_retrieve_objects() {
        let first = ("foo", Object::Number(f64::from(42)));
        let mut environment = Environment::new();

        environment.define(first.0.to_owned(), first.1.clone());

        assert_eq!(Ok(first.1), environment.get(first.0));
    }

    #[test]
    fn it_returns_an_error_if_the_queried_object_doesnt_exist() {
        let foo = "foo";
        let environment = Environment::new();

        assert_eq!(
            Err(RloxError::UndefinedVariable(foo.to_owned())),
            environment.get(foo)
        );
    }

    #[test]
    fn it_can_find_an_object_at_a_higher_level() {
        let first = ("foo", Object::Number(f64::from(42)));
        let second = ("bar", Object::Number(f64::from(100)));
        let mut environment = Environment::new();

        environment.define(first.0.to_owned(), first.1.clone());
        environment.raise();
        environment.define(second.0.to_owned(), second.1.clone());
        environment.raise();

        assert_eq!(Ok(first.1), environment.get(first.0));
    }

    #[test]
    fn it_returns_the_first_matching_object() {
        let common_name = "foo";
        let first = (common_name, Object::Number(f64::from(42)));
        let second = (common_name, Object::Number(f64::from(100)));
        let mut environment = Environment::new();

        environment.define(common_name.to_owned(), first.1.clone());
        environment.raise();
        environment.define(common_name.to_owned(), second.1.clone());

        assert_eq!(Ok(second.1), environment.get(common_name));
    }

    #[test]
    fn it_can_find_an_object_at_a_specified_level() {
        let first = ("foo", Object::Number(f64::from(42)));
        let mut environment = Environment::new();

        environment.define(first.0.to_owned(), first.1.clone());
        environment.raise();
        environment.raise();
        environment.raise();
        environment.raise();

        assert_eq!(Ok(first.1), environment.get_at(4, first.0));
    }

    #[test]
    #[should_panic]
    fn it_panics_if_the_object_doesnt_exist_at_the_specified_level() {
        let first = ("foo", Object::Number(f64::from(42)));
        let mut environment = Environment::new();

        environment.raise();
        environment.raise();
        environment.raise();
        environment.raise();

        let _ = environment.get_at(5, first.0);
    }

    #[test]
    fn it_can_lower_an_environment_after_raising() {
        let first = ("foo", Object::Number(f64::from(42)));
        let mut environment = Environment::new();

        environment.define(first.0.to_owned(), first.1.clone());
        environment.raise();
        assert_eq!(Ok(first.1.clone()), environment.get_at(1, first.0));

        environment.lower();
        assert_eq!(Ok(first.1), environment.get_at(0, first.0));
    }

    #[test]
    fn it_can_update_an_existing_value() {
        let initial = ("foo", Object::Number(f64::from(42)));
        let mut environment = Environment::new();

        environment.define(initial.0.to_owned(), initial.1.clone());
        assert_eq!(Ok(initial.1.clone()), environment.get(initial.0));

        let updated = Object::String("bar".to_owned());
        assert!(environment.assign(initial.0, updated.clone()).is_ok());
        assert_eq!(Ok(updated), environment.get(initial.0));
    }

    #[test]
    fn it_can_update_an_raised_value() {
        let initial = ("foo", Object::Number(f64::from(42)));
        let mut environment = Environment::new();

        environment.define(initial.0.to_owned(), initial.1.clone());
        environment.raise();
        environment.raise();
        environment.raise();
        environment.raise();
        environment.raise();
        environment.raise();
        assert_eq!(Ok(initial.1.clone()), environment.get(initial.0));

        let updated = Object::String("bar".to_owned());
        assert!(environment.assign(initial.0, updated.clone()).is_ok());
        assert_eq!(Ok(updated), environment.get(initial.0));
    }

    #[test]
    fn it_is_an_error_to_update_a_non_existent_value() {
        let foo = "foo";
        let mut environment = Environment::new();

        assert_eq!(
            Err(RloxError::UndefinedVariable(foo.to_owned())),
            environment.assign(foo, Object::Nil)
        );
    }

    #[test]
    fn it_can_be_built_from_an_iterator() {
        let environment = vec![
            ("foo".to_owned(), Object::Number(f64::from(42))),
            ("bar".to_owned(), Object::Nil),
            ("baz".to_owned(), Object::String("baz".to_owned())),
        ]
        .into_iter()
        .collect::<Environment>();

        assert_eq!(Ok(Object::Number(f64::from(42))), environment.get("foo"));
        assert_eq!(Ok(Object::Nil), environment.get("bar"));
        assert_eq!(Ok(Object::String("baz".to_owned())), environment.get("baz"));
    }
}
