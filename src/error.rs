use std::{error, fmt};

/// An enumeration of buffer creation errors
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum Error {
    /// There was not enough underlying data to fulfill some request for raw
    /// bytes.
    NotEnoughData,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::NotEnoughData => write!(
                f,
                "There is not enough underlying raw data to construct an `Arbitrary` instance"
            ),
        }
    }
}

impl error::Error for Error {}

/// A `Result` with the error type fixed as `arbitrary::Error`.
///
/// Either an `Ok(T)` or `Err(arbitrary::Error)`.
pub type Result<T> = std::result::Result<T, Error>;
