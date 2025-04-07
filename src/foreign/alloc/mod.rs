//! Implementations of [`Arbitrary`] for [`alloc`] types,
//!   excluding those in [`core`].
//!
//! [`Arbitrary`]: crate::Arbitrary

mod borrow;
mod boxed;
mod collections;
mod ffi;
mod rc;
mod string;
#[cfg(target_has_atomic = "ptr")]
mod sync;
mod vec;
