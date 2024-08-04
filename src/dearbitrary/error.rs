use std::{error, fmt};

/// An enumeration of dearbitrartion errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The instance's size is unsupported by its corresponding [Arbitrary] type
    TooLarge,
    /// The instance's details are too specific to this platform to be represented by its corresponding [Arbitrary] type,
    TooSpecific
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::TooLarge => write!(
                f,
                "This type instance is too large to be losslessly reconstructed by Arbitrary after dearbitration."
            ),
            Error::TooSpecific => write!(
                f,
                "This type instance is too specific to the platform to be lossly reconstructed by Arbitrary after dearbitration on other platforms."
            ),
        }
    }
}

impl error::Error for Error {}

/// A `Result` with the error type fixed as `arbitrary::Error`.
///
/// Either an `Ok(T)` or `Err(arbitrary::Error)`.
pub type Result<T, E = Error> = std::result::Result<T, E>;

#[cfg(test)]
mod tests {
    #[test]
    fn can_use_custom_error_types_with_result() -> super::Result<(), String> {
        Ok(())
    }
}
