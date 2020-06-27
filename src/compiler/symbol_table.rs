use std::collections::HashMap;

use super::preludes::*;

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Symbol {
    Global { name: String, index: u16 },
}

#[derive(Debug, Default, Clone)]
pub struct SymbolTable {
    store: HashMap<String, Symbol>,
    num_definnitions: u16,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, name: String) -> &Symbol {
        let symbol = Symbol::Global {
            name: name.clone(),
            index: self.num_definnitions,
        };
        self.store.insert(name.clone(), symbol);

        self.num_definnitions += 1;

        self.store.get(&name).unwrap()
    }

    pub fn resolve(&self, name: &str) -> Option<&Symbol> {
        self.store.get(name)
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

        let mut global = SymbolTable::new();

        assert_eq!(global.define("a".to_string()), expected.get("a").unwrap());
        assert_eq!(global.define("b".to_string()), expected.get("b").unwrap());
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
            });
    }
}
