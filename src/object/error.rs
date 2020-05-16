use super::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    pub message: String,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "ERROR: {}", self.message)
    }
}
