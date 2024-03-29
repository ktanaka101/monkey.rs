use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::objects;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Environment {
    outer: Option<Rc<RefCell<Environment>>>,
    scope: HashMap<String, objects::Object>,
}

impl Environment {
    pub fn new_enclose(outer: Rc<RefCell<Environment>>) -> Environment {
        Environment::new(Some(outer))
    }

    pub fn new(outer: Option<Rc<RefCell<Environment>>>) -> Environment {
        Environment {
            outer,
            scope: HashMap::<String, objects::Object>::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<objects::Object> {
        let res = self.scope.get(key);
        if let Some(v) = res {
            Some(v.clone())
        } else if let Some(outer_scope) = &self.outer {
            let scope = outer_scope.borrow();
            scope.get(key)
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: &str, value: objects::Object) -> Option<objects::Object> {
        self.scope.insert(key.to_string(), value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get() {
        let mut env = Environment::new(None);
        let obj = objects::Object::Boolean(objects::Boolean { value: true });

        env.insert("key_a", obj.clone());
        let get_obj = env.get("key_a").unwrap();

        assert_eq!(obj, get_obj);
    }
}
