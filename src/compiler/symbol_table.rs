use std::collections::HashMap;

use super::preludes::*;

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Symbol {
    Global { name: String, index: u16 },
    Local { name: String, index: u16 },
}

#[derive(Debug, Default, Clone)]
pub struct SymbolTable {
    outer: Option<Box<SymbolTable>>,
    store: HashMap<String, Symbol>,
    num_definnitions: u16,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn new_enclosed(outer: Self) -> Self {
        Self {
            outer: Some(Box::new(outer)),
            store: Default::default(),
            num_definnitions: Default::default(),
        }
    }

    pub fn define(&mut self, name: String) -> &Symbol {
        let symbol = if self.outer.is_some() {
            Symbol::Local {
                name: name.clone(),
                index: self.num_definnitions,
            }
        } else {
            Symbol::Global {
                name: name.clone(),
                index: self.num_definnitions,
            }
        };

        self.store.insert(name.clone(), symbol);

        self.num_definnitions += 1;

        self.store.get(&name).unwrap()
    }

    pub fn resolve(&self, name: &str) -> Option<&Symbol> {
        let result: Option<&Symbol> = self.store.get(name);
        if result.is_some() {
            return result;
        }

        if let Some(outer) = &self.outer {
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
            Symbol::Global {
                name: "a".into(),
                index: 0,
            },
        );
        expected.insert(
            "b",
            Symbol::Global {
                name: "b".into(),
                index: 1,
            },
        );
        expected.insert(
            "c",
            Symbol::Local {
                name: "c".into(),
                index: 0,
            },
        );
        expected.insert(
            "d",
            Symbol::Local {
                name: "d".into(),
                index: 1,
            },
        );
        expected.insert(
            "e",
            Symbol::Local {
                name: "e".into(),
                index: 0,
            },
        );
        expected.insert(
            "f",
            Symbol::Local {
                name: "f".into(),
                index: 1,
            },
        );

        let mut global = SymbolTable::new();
        assert_eq!(global.define("a".to_string()), expected.get("a").unwrap());
        assert_eq!(global.define("b".to_string()), expected.get("b").unwrap());

        let mut first_local = SymbolTable::new_enclosed(global);
        assert_eq!(
            first_local.define("c".to_string()),
            expected.get("c").unwrap()
        );
        assert_eq!(
            first_local.define("d".to_string()),
            expected.get("d").unwrap()
        );

        let mut second_local = SymbolTable::new_enclosed(first_local);
        assert_eq!(
            second_local.define("e".to_string()),
            expected.get("e").unwrap()
        );
        assert_eq!(
            second_local.define("f".to_string()),
            expected.get("f").unwrap()
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
                    assert_eq!(result, &expected_symbol);
                }
                Symbol::Local { .. } => unreachable!(),
            });
    }

    #[test]
    fn test_resolve_local() {
        let mut global = SymbolTable::new();
        global.define("a".to_string());
        global.define("b".to_string());

        let mut local = SymbolTable::new_enclosed(global);
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
                    assert_eq!(result, &expected_symbol);
                }
                Symbol::Local { name, .. } => {
                    let result = local.resolve(name).unwrap();
                    assert_eq!(result, &expected_symbol);
                }
            });
    }

    #[test]
    fn test_resolve_nested_local() {
        let mut global = SymbolTable::new();
        global.define("a".to_string());
        global.define("b".to_string());

        let mut first_local = SymbolTable::new_enclosed(global);
        first_local.define("c".to_string());
        first_local.define("d".to_string());

        let mut second_local = SymbolTable::new_enclosed(first_local.clone());
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
                second_local,
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
                        let result = table.resolve(&name).unwrap();
                        assert_eq!(result, &expected_symbol);
                    }
                    Symbol::Local { name, .. } => {
                        let result = table.resolve(&name).unwrap();
                        assert_eq!(result, &expected_symbol);
                    }
                });
        });
    }
}
