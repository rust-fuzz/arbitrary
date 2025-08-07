//! The [`SizeHint`] type, for use with
//! [`Arbitrary::size_hint()`].

use core::cell::Cell;
use core::{fmt, ops};

use crate::Arbitrary;

/// Bounds on the number of bytes an [`Arbitrary::arbitrary()`] implementation might consume.
///
/// A size hint consists of a finite lower bound and a possibly infinite upper bound.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct SizeHint {
    /// Inclusive lower bound.
    lower: usize,

    /// Exclusive upper bound. [`None`] means unbounded.
    ///
    /// Also contains some meta-information about the size hint as a whole.
    upper: Upper,

    out_of_fuel: bool,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Upper {
    Bounded(usize),
    /// The size is known to be unbounded (or overflow [`usize`]).
    Unbounded,
    /// The size is unknown either because a more specific size hint was not given,
    /// or because computation of the size hint was cancelled before it completed.
    /// This is functionally identical to `Unbounded` but prints differently.
    ///
    /// In these cases, the lower bound may also be lower than it should be.
    Unknown,
}

impl SizeHint {
    /// Equal to [`SizeHint::exactly(0)`][Self::exactly].
    pub const ZERO: Self = Self {
        lower: 0,
        upper: Upper::Bounded(0),
        out_of_fuel: false,
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
        out_of_fuel: false,
    };

    /// Indicates that the [`Context`] exhausted its `fuel`.
    pub const OUT_OF_FUEL: Self = Self {
        lower: 0,
        upper: Upper::Unbounded,
        out_of_fuel: true,
    };

    /// Creates a [`SizeHint`] for exactly `size` bytes.
    #[must_use]
    pub const fn exactly(size: usize) -> Self {
        Self {
            lower: size,
            upper: Upper::Bounded(size),
            out_of_fuel: false,
        }
    }

    /// Creates a [`SizeHint`] for `size` bytes or more.
    #[must_use]
    pub const fn at_least(size: usize) -> Self {
        Self {
            lower: size,
            upper: Upper::Unbounded,
            out_of_fuel: false,
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
            out_of_fuel: self.out_of_fuel | rhs.out_of_fuel,
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
            out_of_fuel: self.out_of_fuel | rhs.out_of_fuel,
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

    /// Multiply the bounds by `count`, as if to produce the size hint for constructing an array.
    pub fn repeat(self, count: usize) -> Self {
        Self {
            lower: self.lower.saturating_mul(count),
            upper: match self.upper {
                Upper::Bounded(upper) => upper
                    .checked_mul(count)
                    .map_or(Upper::Unbounded, Upper::Bounded),
                not_bounded => not_bounded,
            },
            out_of_fuel: false,
        }
    }
}

impl fmt::Debug for SizeHint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            lower,
            upper,
            out_of_fuel,
        } = *self;
        match upper {
            Upper::Bounded(upper) => write!(f, "{lower}..={upper}")?,
            Upper::Unbounded => write!(f, "{lower}..")?,
            Upper::Unknown if lower == 0 => write!(f, "(unknown)")?,
            Upper::Unknown => write!(f, "{lower}.. + (unknown)")?,
        }
        if out_of_fuel {
            write!(f, " + (out of fuel)")?;
        }
        Ok(())
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
            out_of_fuel: false,
        }
    }
}
impl From<ops::RangeInclusive<usize>> for SizeHint {
    fn from(range: ops::RangeInclusive<usize>) -> Self {
        Self {
            lower: *range.start(),
            upper: Upper::Bounded(*range.end()),
            out_of_fuel: false,
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
impl ops::AddAssign for SizeHint {
    /// Identical to [`SizeHint::and()`].
    fn add_assign(&mut self, rhs: Self) {
        *self = self.and(rhs)
    }
}
impl ops::BitOr for SizeHint {
    type Output = Self;
    /// Identical to [`SizeHint::or()`].
    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

/// Context passed recursively through [`Arbitrary::size_hint()`] implementations.
///
/// Used to ensure that `size_hint()` cannot execute unbounded recursion through generic types,
/// by terminating the recursion after a certain number of operations, measured by the “fuel” value
/// in this context.
///
/// When you are implementing `size_hint()` for a generic type, use this context by calling
/// [`Context::get()`] instead of calling other `size_hint()` implementations directly,
/// and use `and()`, `or()`, `and_all()`, and `or_all()` to compose size hints.
pub struct Context {
    fuel: Cell<u32>,
}

impl Default for Context {
    fn default() -> Self {
        Self::new(100)
    }
}

impl Context {
    /// Creates a context which allows no more than `fuel` recursive calls.
    pub fn new(fuel: u32) -> Self {
        Context {
            fuel: Cell::new(fuel),
        }
    }

    /// Returns [`T::size_hint()`][Arbitrary::size_hint], and consumes 1 unit of fuel too.
    #[inline]
    pub fn get<'a, T: Arbitrary<'a>>(&self) -> SizeHint {
        if self.consume_fuel() {
            T::size_hint(self)
        } else {
            SizeHint::OUT_OF_FUEL
        }
    }

    /// Consumes 1 unit of fuel if available, and returns whether that fuel was available.
    #[inline(never)]
    fn consume_fuel(&self) -> bool {
        match self.fuel.get().checked_sub(1) {
            Some(new_fuel) => {
                self.fuel.set(new_fuel);
                true
            }
            None => false,
        }
    }
}

/// Creates a new [`Context`] and uses it to ask `T` for its size hint.
///
/// Do not use this function inside of [`size_hint()`] implementations.
pub fn get<'a, T: Arbitrary<'a>>() -> SizeHint {
    T::size_hint(&Context::default())
}

#[cfg(test)]
mod tests {
    use super::{Context, SizeHint};

    #[test]
    fn formatting() {
        fn fmt(s: SizeHint) -> String {
            format!("{s:?}")
        }
        assert_eq!(fmt(SizeHint::ZERO), "0..=0");
        assert_eq!(fmt(SizeHint::UNKNOWN), "(unknown)");
        assert_eq!(fmt(SizeHint::exactly(10)), "10..=10");
        assert_eq!(fmt(SizeHint::at_least(10)), "10..");
        assert_eq!(
            fmt(SizeHint::exactly(10) + SizeHint::UNKNOWN),
            "10.. + (unknown)"
        );
        assert_eq!(
            fmt(SizeHint::exactly(10) + SizeHint::OUT_OF_FUEL),
            "10.. + (out of fuel)"
        );
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

    #[test]
    fn context_short_circuit() {
        struct ShouldNotBeCalled;
        impl<'a> crate::Arbitrary<'a> for ShouldNotBeCalled {
            fn arbitrary(_: &mut crate::Unstructured<'a>) -> crate::Result<Self> {
                unimplemented!()
            }
            fn size_hint(_: &super::Context) -> SizeHint {
                unreachable!()
            }
        }

        // Create a context that allows exactly 2 recursion operations, then show that
        // it does exactly those 2 and no more.
        let context = Context::new(2);
        assert_eq!(
            SizeHint::exactly(3) + SizeHint::OUT_OF_FUEL,
            context.get::<u8>() + context.get::<u16>() + context.get::<ShouldNotBeCalled>(),
        );
    }
}
