//! The [`SizeHint`] type, for use with
//! [`Arbitrary::size_hint()`].

use core::{fmt, ops};

#[cfg(doc)]
use crate::Arbitrary;

pub(crate) const MAX_DEPTH: usize = 20;

/// Bounds on the number of bytes an [`Arbitrary::arbitrary()`] implementation might consume.
///
/// A size hint consists of a finite lower bound and a possibly infinite upper bound.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct SizeHint {
    /// Inclusive lower bound.
    lower: usize,

    /// Exclusive upper bound. [`None`] means unbounded.
    upper: Upper,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Upper {
    Bounded(usize),
    /// The size is known to be unbounded (or overflow [`usize`]).
    Unbounded,
    /// The size is unknown because a more specific size hint was not given.
    /// This is functionally identical to `Unbounded` but prints differently.
    Unknown,
}

impl SizeHint {
    /// Equal to [`SizeHint::exactly(0)`][Self::exactly].
    pub const ZERO: Self = Self {
        lower: 0,
        upper: Upper::Bounded(0),
    };

    /// Indicates that a size hint is not available.
    /// Returned by the default implementation of [`Arbitrary::size_hint()`].
    ///
    /// This is the most uninformative bound: zero to infinity bytes.
    /// In addition, it prints differently from [`SizeHint::at_least(0)`][SizeHint::at_least],
    /// to indicate that it is unknown rather than an unbounded collection.
    pub const UNKNOWN: Self = Self {
        lower: 0,
        upper: Upper::Unknown,
    };

    /// Creates a [`SizeHint`] for exactly `size` bytes.
    #[must_use]
    pub const fn exactly(size: usize) -> Self {
        Self {
            lower: size,
            upper: Upper::Bounded(size),
        }
    }

    /// Creates a [`SizeHint`] for `size` bytes or more.
    #[must_use]
    pub const fn at_least(size: usize) -> Self {
        Self {
            lower: size,
            upper: Upper::Unbounded,
        }
    }

    /// Returns the lower bound on bytes that will be consumed.
    pub const fn lower_bound(self) -> usize {
        self.lower
    }

    /// Returns the upper bound on bytes that will be consumed.
    ///
    /// Returns [`None`] if unlimited bytes could be consumed,
    /// the number of bytes exceeds [`usize::MAX`],
    /// or the bound is unknown.
    pub const fn upper_bound(self) -> Option<usize> {
        match self.upper {
            Upper::Bounded(size) => Some(size),
            Upper::Unbounded => None,
            Upper::Unknown => None,
        }
    }

    /// Protects against potential infinite recursion when calculating size hints
    /// due to indirect type recursion.
    ///
    /// When the depth is not too deep, calls `f` with `depth + 1` to calculate the
    /// size hint.
    ///
    /// Otherwise, returns an error.
    ///
    /// This should be used when implementing [`Arbitrary::size_hint()`]
    /// for generic types.
    pub fn recursion_guard(
        depth: usize,
        f: impl FnOnce(usize) -> Result<Self, crate::MaxRecursionReached>,
    ) -> Result<Self, crate::MaxRecursionReached> {
        if depth > MAX_DEPTH {
            Err(crate::MaxRecursionReached {})
        } else {
            f(depth + 1)
        }
    }

    /// Take the sum of the `self` and `rhs` size hints.
    ///
    /// Use this when an [`Arbitrary::arbitrary()`] implementation is going to consume both
    /// `self` bytes and `rhs` bytes, such as for the fields of a `struct`.
    ///
    /// This operation can also be written as the `+` operator.
    #[inline]
    pub const fn and(self, rhs: Self) -> Self {
        Self {
            lower: self.lower.saturating_add(rhs.lower),
            upper: match (self.upper, rhs.upper) {
                // checked_add causes overflow to become infinite
                (Upper::Bounded(lhs), Upper::Bounded(rhs)) => match lhs.checked_add(rhs) {
                    Some(upper) => Upper::Bounded(upper),
                    None => Upper::Unbounded,
                },
                // If either is explicitly unbounded, then we can accurately say the result is.
                (Upper::Unbounded, _) | (_, Upper::Unbounded) => Upper::Unbounded,
                // If one is unknown and neither is unbounded, result is unknown.
                (Upper::Unknown, _) | (_, Upper::Unknown) => Upper::Unknown,
            },
        }
    }

    /// Take the sum of all of the given size hints.
    ///
    /// If `hints` is empty, returns `SizeHint::exactly(0)`, aka the size of consuming
    /// nothing.
    ///
    /// Use this when an [`Arbitrary::arbitrary()`] implementation is going to consume as many
    /// bytes as all of the hints together, such as for the fields of a `struct`.
    #[inline]
    pub fn and_all(hints: &[Self]) -> Self {
        hints.iter().copied().fold(Self::ZERO, Self::and)
    }

    /// Take the minimum of the lower bounds and maximum of the upper bounds in the
    /// `self` and `rhs` size hints.
    ///
    /// Use this when an [`Arbitrary::arbitrary()`] implementation is going to choose one
    /// alternative and consume that many bytes, such as for the variants of an `enum`.
    ///
    /// This operation can also be written as the `|` operator.
    #[inline]
    pub const fn or(self, rhs: Self) -> Self {
        Self {
            lower: if self.lower < rhs.lower {
                self.lower
            } else {
                rhs.lower
            },
            upper: match (self.upper, rhs.upper) {
                (Upper::Bounded(lhs), Upper::Bounded(rhs)) => {
                    Upper::Bounded(if lhs > rhs { lhs } else { rhs })
                }
                // If either is explicitly unbounded, then we can accurately say the result is.
                (Upper::Unbounded, _) | (_, Upper::Unbounded) => Upper::Unbounded,
                // If one is unknown and neither is unbounded, result is unknown.
                (Upper::Unknown, _) | (_, Upper::Unknown) => Upper::Unknown,
            },
        }
    }

    /// Take the maximum of the `lhs` and `rhs` size hints.
    ///
    /// If `hints` is empty, returns [`SizeHint::ZERO`], aka the size of consuming
    /// nothing.
    ///
    /// Use this when an [`Arbitrary::arbitrary()`] implementation is going to choose one
    /// alternative and consume that many bytes, such as for the variants of an `enum`.
    #[inline]
    pub fn or_all(hints: &[Self]) -> Self {
        if let Some(head) = hints.first().copied() {
            hints[1..].iter().copied().fold(head, Self::or)
        } else {
            Self::ZERO
        }
    }
}

impl fmt::Debug for SizeHint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { lower, upper } = *self;
        match upper {
            Upper::Bounded(upper) => write!(f, "{lower}..={upper}"),
            Upper::Unbounded => write!(f, "{lower}.."),
            Upper::Unknown => write!(f, "{lower}..unknown"),
        }
    }
}

impl Default for SizeHint {
    /// Returns [`SizeHint::UNKNOWN`], the value for when no
    fn default() -> Self {
        Self::UNKNOWN
    }
}

impl From<ops::RangeFrom<usize>> for SizeHint {
    fn from(range: ops::RangeFrom<usize>) -> Self {
        Self {
            lower: range.start,
            upper: Upper::Unbounded,
        }
    }
}
impl From<ops::RangeInclusive<usize>> for SizeHint {
    fn from(range: ops::RangeInclusive<usize>) -> Self {
        Self {
            lower: *range.start(),
            upper: Upper::Bounded(*range.end()),
        }
    }
}

impl ops::RangeBounds<usize> for SizeHint {
    fn start_bound(&self) -> ops::Bound<&usize> {
        ops::Bound::Included(&self.lower)
    }

    fn end_bound(&self) -> ops::Bound<&usize> {
        match &self.upper {
            Upper::Bounded(upper) => ops::Bound::Included(upper),
            Upper::Unbounded | Upper::Unknown => ops::Bound::Unbounded,
        }
    }
}

impl ops::Add for SizeHint {
    type Output = Self;
    /// Identical to [`SizeHint::and()`].
    fn add(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}
impl ops::BitOr for SizeHint {
    type Output = Self;
    /// Identical to [`SizeHint::or()`].
    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::SizeHint;

    #[test]
    fn formatting() {
        fn fmt(s: SizeHint) -> String {
            format!("{s:?}")
        }
        assert_eq!(fmt(SizeHint::ZERO), "0..=0");
        assert_eq!(fmt(SizeHint::UNKNOWN), "0..unknown");
        assert_eq!(fmt(SizeHint::exactly(10)), "10..=10");
        assert_eq!(fmt(SizeHint::at_least(10)), "10..");
    }

    #[test]
    fn and() {
        assert_eq!(
            SizeHint::exactly(5),
            SizeHint::and(SizeHint::exactly(2), SizeHint::exactly(3))
        );
        assert_eq!(
            SizeHint::at_least(5),
            SizeHint::and(SizeHint::exactly(2), SizeHint::at_least(3))
        );
        assert_eq!(
            SizeHint::at_least(5),
            SizeHint::and(SizeHint::at_least(2), SizeHint::exactly(3))
        );
        assert_eq!(
            SizeHint::at_least(5),
            SizeHint::and(SizeHint::at_least(2), SizeHint::at_least(3))
        );
    }

    #[test]
    fn or() {
        assert_eq!(
            SizeHint::from(2..=3),
            SizeHint::or(SizeHint::exactly(2), SizeHint::exactly(3))
        );
        assert_eq!(
            SizeHint::at_least(2),
            SizeHint::or(SizeHint::exactly(2), SizeHint::at_least(3))
        );
        assert_eq!(
            SizeHint::at_least(2),
            SizeHint::or(SizeHint::at_least(2), SizeHint::exactly(3))
        );
        assert_eq!(
            SizeHint::at_least(2),
            SizeHint::or(SizeHint::at_least(2), SizeHint::at_least(3))
        );
    }

    #[test]
    fn and_all() {
        assert_eq!(SizeHint::exactly(0), SizeHint::and_all(&[]));
        assert_eq!(
            SizeHint::exactly(7),
            SizeHint::and_all(&[
                SizeHint::exactly(1),
                SizeHint::exactly(2),
                SizeHint::exactly(4)
            ])
        );
        assert_eq!(
            SizeHint::at_least(7),
            SizeHint::and_all(&[
                SizeHint::exactly(1),
                SizeHint::exactly(2),
                SizeHint::at_least(4)
            ])
        );
        assert_eq!(
            SizeHint::at_least(7),
            SizeHint::and_all(&[
                SizeHint::exactly(1),
                SizeHint::at_least(2),
                SizeHint::exactly(4)
            ])
        );
        assert_eq!(
            SizeHint::at_least(7),
            SizeHint::and_all(&[
                SizeHint::at_least(1),
                SizeHint::exactly(2),
                SizeHint::exactly(4)
            ])
        );
    }

    #[test]
    fn or_all() {
        assert_eq!(SizeHint::exactly(0), SizeHint::or_all(&[]));
        assert_eq!(
            SizeHint::from(1..=4),
            SizeHint::or_all(&[
                SizeHint::exactly(1),
                SizeHint::exactly(2),
                SizeHint::exactly(4)
            ])
        );
        assert_eq!(
            SizeHint::at_least(1),
            SizeHint::or_all(&[
                SizeHint::exactly(1),
                SizeHint::exactly(2),
                SizeHint::at_least(4)
            ])
        );
        assert_eq!(
            SizeHint::at_least(1),
            SizeHint::or_all(&[
                SizeHint::exactly(1),
                SizeHint::at_least(2),
                SizeHint::exactly(4)
            ])
        );
        assert_eq!(
            SizeHint::at_least(1),
            SizeHint::or_all(&[
                SizeHint::at_least(1),
                SizeHint::exactly(2),
                SizeHint::exactly(4)
            ])
        );
    }
}
