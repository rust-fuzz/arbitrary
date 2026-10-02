//! Implementations of [`Arbitrary`] for foreign types.
//!
//! [`Arbitrary`]: crate::Arbitrary

#[cfg(feature = "alloc")]
mod alloc;
mod core;
#[cfg(feature = "std")]
mod std;
