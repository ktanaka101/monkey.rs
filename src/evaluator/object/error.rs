use thiserror::Error as Err;

#[derive(Err, Debug, Clone, PartialEq)]
pub enum Error {
    #[error("{0}")]
    Standard(String),
}
