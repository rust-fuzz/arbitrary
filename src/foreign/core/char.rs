use {
    crate::{Arbitrary, ArbitraryInRange, Error, Result, Unstructured},
    core::ops::{Bound, RangeBounds},
};

/// The lower limit of the surrogates block:
const SURROGATES_LOWER: u32 = 0xd800;

/// The lower limit of the surrogates block:
const SURROGATES_UPPER: u32 = 0xdfff;

fn map_char_bound(character: Bound<&char>) -> Bound<u32> {
    match character {
        Bound::Included(character) => Bound::Included(u32::from(*character)),
        Bound::Excluded(character) => Bound::Excluded(u32::from(*character)),
        Bound::Unbounded => Bound::Unbounded,
    }
}

impl<'a> ArbitraryInRange<'a> for char {
    type Bound = Self;

    fn arbitrary_in_range<R>(u: &mut Unstructured<'a>, range: &R) -> Result<Self>
    where
        R: RangeBounds<Self::Bound>,
    {
        let minimum = map_char_bound(range.start_bound());
        let maximum = map_char_bound(range.end_bound());
        let range = (minimum, maximum);

        // In the range of valid unicode characters (['\0', char::MAX]),
        //   there is a block called surrogates ([SURROGATES_LOWER, SURROGATES_UPPER]).
        let character = match (
            range.contains(&SURROGATES_LOWER),
            range.contains(&SURROGATES_UPPER),
        ) {
            // If SURROGATES_LOWER is not in range but SURROGATES_UPPER is, fix the lower bound:
            (false, true) => {
                u32::arbitrary_in_range(u, &(Bound::Excluded(SURROGATES_UPPER), maximum))
            }

            // If SURROGATES_LOWER is in range but SURROGATES_UPPER not, fix the upper bound:
            (true, false) => {
                u32::arbitrary_in_range(u, &(minimum, Bound::Excluded(SURROGATES_LOWER)))
            }

            // If the entire surrogate-block is inside range, choose one of:
            // * minimum .. SURROGATES_LOWER
            // * SURROGATES_UPPER .. maximum
            (true, true) => bool::arbitrary(u).and_then(|coin_flip| {
                let range = match coin_flip {
                    true => (Bound::Excluded(SURROGATES_UPPER), maximum),
                    false => (minimum, Bound::Excluded(SURROGATES_LOWER)),
                };
                u32::arbitrary_in_range(u, &range)
            }),

            // If neither the lower nor upper bound of the surrogate block is within the range,
            //   the range is either entirely below, above or within the surrogate block.
            // In this case, either all values of the given range are valid characters or none.
            _ => u32::arbitrary_in_range(u, &(minimum, maximum)),
        };

        // InvalidRange will be returned if range is entirely within the surrogate block.
        char::from_u32(character?).ok_or(Error::InvalidRange)
    }
}

impl<'a> Arbitrary<'a> for char {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        char::arbitrary_in_range(u, &..)
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        <u32 as Arbitrary<'a>>::size_hint(depth)
    }
}
