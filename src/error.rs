/// An enumeration of buffer creation errors
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum Error {
    /// The input buffer is empty, causing construction of some buffer types to
    /// fail
    EmptyInput,

    /// There is not enough underlying data to fulfill a request for raw bytes.
    NotEnoughData,
}

/// A `Result` with the error type fixed as `arbitrary::Error`.
///
/// Either an `Ok(T)` or `Err(arbitrary::Error)`.
pub type Result<T> = std::result::Result<T, Error>;
