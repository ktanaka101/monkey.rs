use std::collections::HashMap;

use super::preludes::*;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Symbol {
    Global { name: String, index: u16 },
    Local { name: String, index: u8 },
    Builtin { name: String, index: u8 },
}

#[derive(Debug, Default, Clone)]
pub struct SymbolTable {
    pub outer: Option<Rc<RefCell<SymbolTable>>>,
    store: HashMap<String, Rc<RefCell<Symbol>>>,
    pub num_definitions: u16,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn new_enclosed(outer: Rc<RefCell<Self>>) -> Self {
        Self {
            outer: Some(outer),
            store: Default::default(),
            num_definitions: Default::default(),
        }
    }

    pub fn define(&mut self, name: String) -> Rc<RefCell<Symbol>> {
        let symbol = if self.outer.is_some() {
            Symbol::Local {
                name: name.clone(),
                index: u8::try_from(self.num_definitions).unwrap(),
            }
        } else {
            Symbol::Global {
                name: name.clone(),
                index: self.num_definitions,
            }
        };
        let symbol = Rc::new(RefCell::new(symbol));

        self.store.insert(name.clone(), Rc::clone(&symbol));

        self.num_definitions += 1;

        symbol
    }

    pub fn define_builtin(&mut self, index: u8, name: String) -> Rc<RefCell<Symbol>> {
        let symbol = Symbol::Builtin {
            index,
            name: name.clone(),
        };
        let symbol = Rc::new(RefCell::new(symbol));

        self.store.insert(name, Rc::clone(&symbol));

        symbol
    }

    pub fn resolve(&self, name: &str) -> Option<Rc<RefCell<Symbol>>> {
        let result = self.store.get(name).map(|sym| Rc::clone(&sym));
        if result.is_some() {
            return result;
        }

        if let Some(outer) = &self.outer {
            let outer = outer.borrow();
            outer.resolve(name)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_define() {
        let mut expected = HashMap::new();
        expected.insert(
            "a",
            Rc::new(RefCell::new(Symbol::Global {
                name: "a".into(),
                index: 0,
            })),
        );
        expected.insert(
            "b",
            Rc::new(RefCell::new(Symbol::Global {
                name: "b".into(),
                index: 1,
            })),
        );
        expected.insert(
            "c",
            Rc::new(RefCell::new(Symbol::Local {
                name: "c".into(),
                index: 0,
            })),
        );
        expected.insert(
            "d",
            Rc::new(RefCell::new(Symbol::Local {
                name: "d".into(),
                index: 1,
            })),
        );
        expected.insert(
            "e",
            Rc::new(RefCell::new(Symbol::Local {
                name: "e".into(),
                index: 0,
            })),
        );
        expected.insert(
            "f",
            Rc::new(RefCell::new(Symbol::Local {
                name: "f".into(),
                index: 1,
            })),
        );

        let mut global = SymbolTable::new();
        assert_eq!(
            global.define("a".to_string()),
            Rc::clone(expected.get("a").unwrap())
        );
        assert_eq!(
            global.define("b".to_string()),
            Rc::clone(expected.get("b").unwrap())
        );

        let mut first_local = SymbolTable::new_enclosed(Rc::new(RefCell::new(global)));
        assert_eq!(
            first_local.define("c".to_string()),
            Rc::clone(expected.get("c").unwrap())
        );
        assert_eq!(
            first_local.define("d".to_string()),
            Rc::clone(expected.get("d").unwrap())
        );

        let mut second_local = SymbolTable::new_enclosed(Rc::new(RefCell::new(first_local)));
        assert_eq!(
            second_local.define("e".to_string()),
            Rc::clone(expected.get("e").unwrap())
        );
        assert_eq!(
            second_local.define("f".to_string()),
            Rc::clone(expected.get("f").unwrap())
        );
    }

    #[test]
    fn test_resolve_global() {
        let mut global = SymbolTable::new();
        global.define("a".to_string());
        global.define("b".to_string());

        let expected = vec![
            Symbol::Global {
                name: "a".into(),
                index: 0,
            },
            Symbol::Global {
                name: "b".into(),
                index: 1,
            },
        ];

        expected
            .into_iter()
            .for_each(|expected_symbol| match &expected_symbol {
                Symbol::Global { name, .. } => {
                    let result = global.resolve(name).unwrap();
                    assert_eq!(result, Rc::new(RefCell::new(expected_symbol)));
                }
                _ => unreachable!(),
            });
    }

    #[test]
    fn test_resolve_local() {
        let mut global = SymbolTable::new();
        global.define("a".to_string());
        global.define("b".to_string());

        let mut local = SymbolTable::new_enclosed(Rc::new(RefCell::new(global)));
        local.define("c".to_string());
        local.define("d".to_string());

        let expected = vec![
            Symbol::Global {
                name: "a".to_string(),
                index: 0,
            },
            Symbol::Global {
                name: "b".to_string(),
                index: 1,
            },
            Symbol::Local {
                name: "c".to_string(),
                index: 0,
            },
            Symbol::Local {
                name: "d".to_string(),
                index: 1,
            },
        ];

        expected
            .into_iter()
            .for_each(|expected_symbol| match &expected_symbol {
                Symbol::Global { name, .. } => {
                    let result = local.resolve(name).unwrap();
                    assert_eq!(result, Rc::new(RefCell::new(expected_symbol)));
                }
                Symbol::Local { name, .. } => {
                    let result = local.resolve(name).unwrap();
                    assert_eq!(result, Rc::new(RefCell::new(expected_symbol)));
                }
                _ => unreachable!(),
            });
    }

    #[test]
    fn test_resolve_nested_local() {
        let mut global = SymbolTable::new();
        global.define("a".to_string());
        global.define("b".to_string());

        let mut first_local = SymbolTable::new_enclosed(Rc::new(RefCell::new(global)));
        first_local.define("c".to_string());
        first_local.define("d".to_string());
        let first_local = Rc::new(RefCell::new(first_local));

        let mut second_local = SymbolTable::new_enclosed(Rc::clone(&first_local));
        second_local.define("e".to_string());
        second_local.define("f".to_string());

        let tests = vec![
            (
                first_local,
                vec![
                    Symbol::Global {
                        name: "a".to_string(),
                        index: 0,
                    },
                    Symbol::Global {
                        name: "b".to_string(),
                        index: 1,
                    },
                    Symbol::Local {
                        name: "c".to_string(),
                        index: 0,
                    },
                    Symbol::Local {
                        name: "d".to_string(),
                        index: 1,
                    },
                ],
            ),
            (
                Rc::new(RefCell::new(second_local)),
                vec![
                    Symbol::Global {
                        name: "a".to_string(),
                        index: 0,
                    },
                    Symbol::Global {
                        name: "b".to_string(),
                        index: 1,
                    },
                    Symbol::Local {
                        name: "e".to_string(),
                        index: 0,
                    },
                    Symbol::Local {
                        name: "f".to_string(),
                        index: 1,
                    },
                ],
            ),
        ];

        tests.into_iter().for_each(|(table, symbols)| {
            symbols
                .into_iter()
                .for_each(|expected_symbol| match &expected_symbol {
                    Symbol::Global { name, .. } => {
                        let table = table.borrow();
                        let result = table.resolve(&name).unwrap();
                        assert_eq!(result, Rc::new(RefCell::new(expected_symbol)));
                    }
                    Symbol::Local { name, .. } => {
                        let table = table.borrow();
                        let result = table.resolve(&name).unwrap();
                        assert_eq!(result, Rc::new(RefCell::new(expected_symbol)));
                    }
                    _ => unreachable!(),
                });
        });
    }

    #[test]
    fn test_define_resolve_builtins() {
        let global = Rc::new(RefCell::new(SymbolTable::new()));
        let first_local = Rc::new(RefCell::new(SymbolTable::new_enclosed(Rc::clone(&global))));
        let second_local = Rc::new(RefCell::new(SymbolTable::new_enclosed(Rc::clone(
            &first_local,
        ))));

        let expected = vec![("a", 0), ("c", 1), ("e", 2), ("f", 3)];
        expected.iter().for_each(|(name, index)| {
            global.borrow_mut().define_builtin(*index, name.to_string());
        });

        vec![global, first_local, second_local]
            .into_iter()
            .for_each(move |symbol_table| {
                expected.iter().for_each(|(name, index)| {
                    let result = symbol_table.borrow().resolve(name);
                    if let Some(result) = result {
                        assert_eq!(
                            *result.borrow(),
                            Symbol::Builtin {
                                index: *index,
                                name: name.to_string()
                            }
                        );
                    } else {
                        panic!("name {} not resolvable", name);
                    }
                });
            });
    }
}
