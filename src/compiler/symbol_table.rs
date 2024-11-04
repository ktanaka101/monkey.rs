use std::collections::HashMap;

use super::preludes::*;
use crate::evaluator::builtin;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Symbol {
    Global { name: String, index: u16 },
    Local { name: String, index: u8 },
    Builtin { name: String, index: u8 },
    Free { name: String, index: u8 },
    Function { name: String, index: u8 },
}

impl Symbol {
    fn name(&self) -> String {
        match self {
            Symbol::Global { name, .. }
            | Symbol::Function { name, .. }
            | Symbol::Local { name, .. }
            | Symbol::Builtin { name, .. }
            | Symbol::Free { name, .. } => name,
        }
        .clone()
    }
}

#[derive(Debug, Default, Clone)]
pub struct SymbolTable {
    pub outer: Option<Rc<RefCell<SymbolTable>>>,
    store: HashMap<String, Rc<RefCell<Symbol>>>,
    pub num_definitions: u16,
    pub free_symbols: Vec<Rc<RefCell<Symbol>>>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn new_with_builtin() -> Self {
        let mut sym_table = Self::new();
        builtin::Function::iterator()
            .enumerate()
            .for_each(|(i, func)| {
                sym_table.define_builtin(u8::try_from(i).unwrap(), func.name().to_string());
            });

        sym_table
    }

    pub fn new_enclosed(outer: Rc<RefCell<Self>>) -> Self {
        Self {
            outer: Some(outer),
            store: Default::default(),
            num_definitions: Default::default(),
            free_symbols: Default::default(),
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

        self.store.insert(name, Rc::clone(&symbol));

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

    pub fn define_free(&mut self, original: Rc<RefCell<Symbol>>) -> Rc<RefCell<Symbol>> {
        self.free_symbols.push(Rc::clone(&original));

        let name = original.borrow().name();

        let symbol = Rc::new(RefCell::new(Symbol::Free {
            name: name.clone(),
            index: u8::try_from(self.free_symbols.len()).unwrap() - 1,
        }));

        self.store.insert(name, Rc::clone(&symbol));

        symbol
    }

    pub fn resolve(&mut self, name: &str) -> Option<Rc<RefCell<Symbol>>> {
        let result = self.store.get(name).map(Rc::clone);
        if result.is_some() {
            return result;
        }

        if let Some(outer) = &self.outer {
            let result = outer.borrow_mut().resolve(name);
            if let Some(res) = result {
                match *res.borrow() {
                    Symbol::Global { .. } | Symbol::Builtin { .. } | Symbol::Function { .. } => {
                        Some(Rc::clone(&res))
                    }
                    Symbol::Free { .. } | Symbol::Local { .. } => {
                        let free = self.define_free(Rc::clone(&res));
                        Some(free)
                    }
                }
            } else {
                result
            }
        } else {
            None
        }
    }

    pub fn define_function_name(&mut self, name: String) -> Rc<RefCell<Symbol>> {
        let symbol = Rc::new(RefCell::new(Symbol::Function {
            name: name.clone(),
            index: 0,
        }));
        self.store.insert(name, Rc::clone(&symbol));

        symbol
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
                        let mut table = table.borrow_mut();
                        let result = table.resolve(name).unwrap();
                        assert_eq!(result, Rc::new(RefCell::new(expected_symbol)));
                    }
                    Symbol::Local { name, .. } => {
                        let mut table = table.borrow_mut();
                        let result = table.resolve(name).unwrap();
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

        let expected = [("a", 0), ("c", 1), ("e", 2), ("f", 3)];
        expected.iter().for_each(|(name, index)| {
            global.borrow_mut().define_builtin(*index, name.to_string());
        });

        vec![global, first_local, second_local]
            .into_iter()
            .for_each(move |symbol_table| {
                expected.iter().for_each(|(name, index)| {
                    let result = symbol_table.borrow_mut().resolve(name);
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

    #[test]
    fn test_resolve_free() {
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

        type Symbols = Vec<Symbol>;
        let tests: Vec<(Rc<RefCell<SymbolTable>>, Symbols, Symbols)> = vec![
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
                vec![],
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
                    Symbol::Free {
                        name: "c".to_string(),
                        index: 0,
                    },
                    Symbol::Free {
                        name: "d".to_string(),
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
                vec![
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
        ];

        tests
            .into_iter()
            .for_each(|(symbol_table, expected_symbols, expected_free_symbols)| {
                expected_symbols.into_iter().for_each(|sym| {
                    let result = symbol_table.borrow_mut().resolve(&sym.name());
                    if let Some(result) = result {
                        assert_eq!(*result.borrow(), sym);
                    } else {
                        panic!("name {} not resolvable", sym.name());
                    }
                });

                assert_eq!(
                    symbol_table.borrow().free_symbols.len(),
                    expected_free_symbols.len()
                );

                expected_free_symbols
                    .iter()
                    .enumerate()
                    .for_each(|(i, sym)| {
                        let table = symbol_table.borrow();
                        let result = table.free_symbols[i].borrow();
                        assert_eq!(&*result, sym);
                    });
            });
    }

    #[test]
    fn test_resolve_unresolveable_free() {
        let mut global = SymbolTable::new();
        global.define("a".to_string());

        let mut first_local = SymbolTable::new_enclosed(Rc::new(RefCell::new(global)));
        first_local.define("c".to_string());

        let mut second_local = SymbolTable::new_enclosed(Rc::new(RefCell::new(first_local)));
        second_local.define("e".to_string());
        second_local.define("f".to_string());

        let expected = vec![
            Symbol::Global {
                name: "a".to_string(),
                index: 0,
            },
            Symbol::Free {
                name: "c".to_string(),
                index: 0,
            },
            Symbol::Local {
                name: "e".to_string(),
                index: 0,
            },
            Symbol::Local {
                name: "f".to_string(),
                index: 1,
            },
        ];

        expected.into_iter().for_each(|expected_sym| {
            let result = second_local.resolve(&expected_sym.name());
            if let Some(result) = result {
                assert_eq!(*result.borrow(), expected_sym);
            } else {
                panic!("name {} not resolvable", expected_sym.name())
            }
        });

        let expected_unresolvable = ["b", "d"];

        expected_unresolvable.iter().for_each(|name| {
            if second_local.resolve(name).is_some() {
                panic!("name {} resolved, but was expected not to", name);
            }
        });
    }

    #[test]
    fn test_define_and_rresolve_function_name() {
        let mut global = SymbolTable::new();
        global.define_function_name("a".to_string());

        let expected = Symbol::Function {
            name: "a".to_string(),
            index: 0,
        };

        let result = global.resolve(&expected.name()).unwrap();
        assert_eq!(*result.borrow(), expected);
    }

    #[test]
    fn test_shadowing_function_name() {
        let mut global = SymbolTable::new();
        global.define_function_name("a".to_string());
        global.define("a".to_string());

        let expected = Symbol::Global {
            name: "a".to_string(),
            index: 0,
        };

        let result = global.resolve(&expected.name()).unwrap();

        assert_eq!(*result.borrow(), expected);
    }
}
