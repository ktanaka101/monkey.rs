use thiserror::Error as Err;

#[derive(Err, Debug, Clone, PartialEq, Eq)]
pub enum Error {
    #[error("{0}")]
    Standard(String),
}
