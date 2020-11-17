use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::iter::FromIterator;

use super::{Object, Result, RloxError};

#[derive(Debug, Clone, PartialEq)]
enum State {
    Normal,
    Closure(usize),
}

/// A container for the interpreter's environment that can be arbitrarily nested.
#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    values: Vec<HashMap<String, Object>>,
    closures: Vec<Vec<HashMap<String, Object>>>,
    state: State,
}

impl Environment {
    /// Creates a new empty environment.
    #[must_use]
    pub fn new() -> Self {
        Environment {
            values: vec![HashMap::new()],
            closures: Vec::new(),
            state: State::Normal,
        }
    }

    /// Returns a shared reference to the outermost environment.
    ///
    /// SAFETY: Getting values at index 0 is *always* safe since creating
    /// and environment object *always* creates a vector with one element.
    pub fn globals<'a>(&'a mut self) -> &'a HashMap<String, Object> {
        assert!(self.values.len() > 1);
        unsafe { self.values.get_unchecked(0) }
    }

    /// Inserts `(name : value)` into self's environment
    pub fn define(&mut self, name: String, value: Object) {
        let values = match self.state {
            State::Normal => &mut self.values,
            State::Closure(index) => self.closures.get_mut(index).unwrap(),
        };

        // SAFETY: Since there will always be at least one element in the values vector, unwrapping
        // the last element is safe.
        assert!(values.len() >= 1);
        values.last_mut().unwrap().insert(name, value);
    }

    /// Returns the value of `name` in the first environment it's found in.
    ///
    /// # Returns
    /// Returns `Ok(Object)` in the first environment `name` is found in.
    /// Returns `Err(RloxError::UndefinedVariable(name))` if `name` is not found
    /// in any environment.
    pub fn get(&self, name: &str) -> Result<Object> {
        let values = match self.state {
            State::Normal => &self.values,
            State::Closure(index) => self.closures.get(index).unwrap(),
        };

        for env in values.iter().rev() {
            if let Some(s) = env.get(name) {
                return Ok(s.clone());
            }
        }

        Err(RloxError::UndefinedVariable(name.to_owned()))
    }

    /// Assigns `value` in the first environment `name` is found in.
    pub fn assign(&mut self, name: &str, value: Object) -> Result<Object> {
        let values = match self.state {
            State::Normal => &mut self.values,
            State::Closure(index) => self.closures.get_mut(index).unwrap(),
        };

        for env in values.iter_mut().rev() {
            if let Entry::Occupied(mut e) = env.entry(name.to_owned()) {
                e.insert(value);
                return Ok(e.get().clone());
            }
        }

        Err(RloxError::UndefinedVariable(name.to_owned()))
    }

    /// Raises an environment up a single level
    ///
    /// # Note
    /// This is the inverse of `Environment::lower`.
    pub fn raise(&mut self) {
        let values = match self.state {
            State::Normal => &mut self.values,
            // TODO handle errors
            State::Closure(index) => self.closures.get_mut(index).unwrap(),
        };

        values.push(HashMap::new());
    }

    /// Collapses the environment 1 level.
    ///
    /// # Panics
    /// `lower` is infallible. It is the responsibility of the programmer to
    /// ensure that the current environment has an enclosing environment and .
    /// Failure to meet the condition above will crash rlox.
    ///
    /// # Note
    /// This is the inverse of `Environment::raise`.
    pub fn lower(&mut self) {
        let values = match self.state {
            State::Normal => &mut self.values,
            // TODO handle errors
            State::Closure(index) => self.closures.get_mut(index).unwrap(),
        };
        assert_ne!(values.len(), 1);

        values.pop();
    }

    /// Gets `name` in environment at `distance`
    ///
    /// Walks through the chain of `self`'s environment to distance and then searches for `name`.
    ///
    /// # Panics
    /// Panics if `distance` is unreachable.
    pub fn get_at(&self, distance: usize, name: &str) -> Result<Object> {
        let values = match self.state {
            State::Normal => &self.values,
            State::Closure(index) => self.closures.get(index).unwrap(),
        };

        assert!(distance < values.len());
        match values.get(distance).unwrap().get(name) {
            Some(obj) => return Ok(obj.clone()),
            None => {
                dbg!(&self);
                panic!(format!("{} does not exist at {}", name, distance))
            }
        }
    }

    pub fn close_over(&mut self) -> Option<usize> {
        if self.is_global() {
            None
        } else {
            // Expensive!
            self.closures.push(self.values.clone());
            Some(self.closures.len() - 1)
        }
    }

    pub fn restore_closure(&mut self, index: usize) {
        self.state = State::Closure(index);
    }

    pub fn restore_environment(&mut self) {
        self.state = State::Normal;
    }

    fn is_global(&self) -> bool {
        self.values.len() == 1
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
            values: vec![values],
            closures: Vec::new(),
            state: State::Normal,
        }
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

        assert_eq!(Ok(first.1), environment.get_at(0, first.0));
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

        let _ = environment.get_at(0, first.0);
    }

    #[test]
    fn it_can_lower_an_environment_after_raising() {
        let first = ("foo", Object::Number(f64::from(42)));
        let mut environment = Environment::new();

        environment.define(first.0.to_owned(), first.1.clone());
        environment.raise();
        assert_eq!(Ok(first.1.clone()), environment.get_at(0, first.0));

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

    // Environment::define(foo)
    // +---------+
    // | 1       |
    // +---------+
    // | Foo     |
    // +---------+
    //
    // Environment::raise()
    // Environment::define(bar)
    // +---------+
    // +---------+---------+
    // | 1       | 2       |
    // +---------+---------+
    // | Foo     | Bar     |
    // +---------+---------+
    //
    // Environment::raise()
    // Environment::define(baz)
    // +---------+---------+---------+
    // | 1       | 2       | 3       |
    // +---------+---------+---------+
    // | Foo     | Bar     | Baz     |
    // +---------+---------+---------+
    //
    // Environment::close_over()
    //            +--- Closure
    //            |
    //            |
    //  +---------+----------+
    //  V                    V
    // +---------+---------+---------+
    // | 1       | 2       | 3       |
    // +---------+---------+---------+
    // | Foo     | Bar     | Baz     |
    // +---------+---------+---------+
    //
    // Environment::lower()
    // +---------+---------+
    // | 1       | 2       |
    // +---------+---------+
    // | Foo     | Bar     |
    // +---------+---------+
    //
    // Environment::lower()
    // +---------+
    // | 1       |
    // +---------+
    // | Foo     |
    // +---------+
    //
    // Environment::restore_closure()
    // +---------+---------+---------+
    // | 1       | 2       | 3       |
    // +---------+---------+---------+
    // | Foo     | Bar     | Baz     |
    // +---------+---------+---------+
    //
    // Environment::restore_environment
    // +---------+
    // | 1       |
    // +---------+
    // | Foo     |
    // +---------+
    #[test]
    fn it_can_close_over_an_environment() {
        let foo = ("foo", Object::Number(f64::from(42)));
        let bar = ("bar", Object::Number(f64::from(100)));
        let baz = ("baz", Object::Number(f64::from(256)));

        let mut environment = Environment::new();
        environment.define(foo.0.to_owned(), foo.1.clone());

        environment.raise();
        environment.define(bar.0.to_owned(), bar.1.clone());

        environment.raise();
        environment.define(baz.0.to_owned(), baz.1.clone());
        let index = environment.close_over();

        environment.lower();
        environment.lower();

        assert_eq!(Ok(foo.1.clone()), environment.get(foo.0));
        assert_eq!(
            Err(RloxError::UndefinedVariable(bar.0.to_owned())),
            environment.get(bar.0)
        );
        assert_eq!(
            Err(RloxError::UndefinedVariable(bar.0.to_owned())),
            environment.get(bar.0)
        );

        environment.restore_closure(index.unwrap());
        assert_eq!(Ok(foo.1.clone()), environment.get(foo.0));
        assert_eq!(Ok(bar.1.clone()), environment.get(bar.0));
        assert_eq!(Ok(baz.1.clone()), environment.get(baz.0));

        environment.restore_environment();
        assert_eq!(Ok(foo.1.clone()), environment.get(foo.0));
        assert_eq!(
            Err(RloxError::UndefinedVariable(bar.0.to_owned())),
            environment.get(bar.0)
        );
        assert_eq!(
            Err(RloxError::UndefinedVariable(bar.0.to_owned())),
            environment.get(bar.0)
        );
    }
}
