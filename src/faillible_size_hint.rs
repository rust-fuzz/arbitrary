//! Utilities for working with and combining the results of
//! [`Arbitrary::faillible_size_hint`][crate::Arbitrary::faillible_size_hint].

use crate::{size_hint::MAX_DEPTH, MaxRecursionReached};

/// Protects against potential infinite recursion when calculating size hints
/// due to indirect type recursion.
///
/// When the depth is not too deep, calls `f` with `depth + 1` to calculate the
/// size hint.
///
/// Otherwise, returns an error.
#[inline]
pub fn recursion_guard(
    depth: usize,
    f: impl FnOnce(usize) -> Result<(usize, Option<usize>), MaxRecursionReached>,
) -> Result<(usize, Option<usize>), MaxRecursionReached> {
    if depth > MAX_DEPTH {
        Err(MaxRecursionReached)
    } else {
        f(depth + 1)
    }
}
