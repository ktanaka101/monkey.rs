use std::collections::HashMap;

use super::prelude::*;
use super::{HashableObject, Object};

pub type HashPairs = HashMap<HashableObject, Object>;

#[derive(Debug, Clone, PartialEq)]
pub struct Hash {
    pub pairs: HashPairs,
}

impl Display for Hash {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let out = self
            .pairs
            .iter()
            .map(|(k, v)| format!("{}, {}", k, v))
            .collect::<Vec<String>>()
            .join("");

        write!(f, "{}", out)
    }
}
