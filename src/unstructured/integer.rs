//! FIXME: Missing Documentation.

use core::{
    fmt::Debug,
    mem,
    ops::{BitOr, Rem, Shl, Shr, Sub},
};

/// A trait that is implemented for all of the primitive integers:
///
/// * `u8`
/// * `u16`
/// * `u32`
/// * `u64`
/// * `u128`
/// * `usize`
/// * `i8`
/// * `i16`
/// * `i32`
/// * `i64`
/// * `i128`
/// * `isize`
///
/// Don't implement this trait yourself.
pub trait Int:
    Copy
    + Debug
    + PartialOrd
    + Ord
    + Sub<Self, Output = Self>
    + Rem<Self, Output = Self>
    + Shr<Self, Output = Self>
    + Shl<usize, Output = Self>
    + BitOr<Self, Output = Self>
{
    #[doc(hidden)]
    type Unsigned: Int;

    #[doc(hidden)]
    type Array: Default + AsMut<[u8]>;

    #[doc(hidden)]
    const ZERO: Self;

    #[doc(hidden)]
    const ONE: Self;

    #[doc(hidden)]
    const MIN: Self;

    #[doc(hidden)]
    const MAX: Self;

    #[doc(hidden)]
    fn from_u8(b: u8) -> Self;

    #[doc(hidden)]
    fn from_bytes(bytes: Self::Array) -> Self;

    #[doc(hidden)]
    fn from_usize(u: usize) -> Self;

    #[doc(hidden)]
    fn checked_add(self, rhs: Self) -> Option<Self>;

    #[doc(hidden)]
    fn wrapping_add(self, rhs: Self) -> Self;

    #[doc(hidden)]
    fn wrapping_sub(self, rhs: Self) -> Self;

    #[doc(hidden)]
    fn to_unsigned(self) -> Self::Unsigned;

    #[doc(hidden)]
    fn from_unsigned(unsigned: Self::Unsigned) -> Self;
}

macro_rules! impl_int {
    ( $( $ty:ty : $unsigned_ty: ty ; )* ) => {
        $(
            impl Int for $ty {
                type Unsigned = $unsigned_ty;

                type Array = [u8; mem::size_of::<$ty>()];

                const ZERO: Self = 0;

                const ONE: Self = 1;

                const MIN: Self = Self::MIN;

                const MAX: Self = Self::MAX;

                fn from_u8(b: u8) -> Self {
                    b as Self
                }

                fn from_bytes(bytes: Self::Array) -> Self {
                    Self::from_le_bytes(bytes)
                }

                fn from_usize(u: usize) -> Self {
                    u as Self
                }

                fn checked_add(self, rhs: Self) -> Option<Self> {
                    <$ty>::checked_add(self, rhs)
                }

                fn wrapping_add(self, rhs: Self) -> Self {
                    <$ty>::wrapping_add(self, rhs)
                }

                fn wrapping_sub(self, rhs: Self) -> Self {
                    <$ty>::wrapping_sub(self, rhs)
                }

                fn to_unsigned(self) -> Self::Unsigned {
                    self as $unsigned_ty
                }

                fn from_unsigned(unsigned: $unsigned_ty) -> Self {
                    unsigned as Self
                }
            }
        )*
    }
}

impl_int! {
    u8: u8;
    u16: u16;
    u32: u32;
    u64: u64;
    u128: u128;
    usize: usize;
    i8: u8;
    i16: u16;
    i32: u32;
    i64: u64;
    i128: u128;
    isize: usize;
}
