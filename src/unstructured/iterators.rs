//! FIXME: Missing Documentation.

use {
    super::Unstructured,
    crate::{Arbitrary, ArbitraryInRange, Result},
    core::{marker::PhantomData, ops::RangeBounds},
};

/// Utility iterator produced by [`Unstructured::arbitrary_iter`]
pub struct ArbitraryIter<'a, 'b, ElementType> {
    u: &'b mut Unstructured<'a>,
    _marker: PhantomData<ElementType>,
}

impl<'a, 'b, ElementType> ArbitraryIter<'a, 'b, ElementType> {
    /// Construct a new arbitrary iterator consuming all the remaining bytes.
    pub fn new(u: &'b mut Unstructured<'a>) -> Self {
        Self {
            u,
            _marker: PhantomData,
        }
    }
}

impl<'a, 'b, ElementType: Arbitrary<'a>> Iterator for ArbitraryIter<'a, 'b, ElementType> {
    type Item = Result<ElementType>;
    fn next(&mut self) -> Option<Result<ElementType>> {
        let keep_going = self.u.arbitrary().unwrap_or(false);
        if keep_going {
            Some(Arbitrary::arbitrary(self.u))
        } else {
            None
        }
    }
}

/// Utility iterator produced by [`Unstructured::arbitrary_in_range_iter`]
pub struct ArbitraryInRangeIter<'a, 'u, 'r, ElementType, Range>
where
    ElementType: ArbitraryInRange<'a>,
    Range: RangeBounds<ElementType::Bound>,
{
    u: &'u mut Unstructured<'a>,
    range: &'r Range,
    _marker: PhantomData<ElementType>,
}

impl<'a, 'u, 'r, ElementType, Range> ArbitraryInRangeIter<'a, 'u, 'r, ElementType, Range>
where
    ElementType: ArbitraryInRange<'a>,
    Range: RangeBounds<ElementType::Bound>,
{
    /// Construct a new arbitrary iterator consuming all the remaining bytes.
    pub fn new(u: &'u mut Unstructured<'a>, range: &'r Range) -> Self {
        Self {
            u,
            range,
            _marker: PhantomData,
        }
    }
}

impl<'a, 'u, 'r, ElementType, Range> Iterator
    for ArbitraryInRangeIter<'a, 'u, 'r, ElementType, Range>
where
    ElementType: ArbitraryInRange<'a>,
    Range: RangeBounds<ElementType::Bound>,
{
    type Item = Result<ElementType>;
    fn next(&mut self) -> Option<Result<ElementType>> {
        let keep_going = self.u.arbitrary().unwrap_or(false);
        if keep_going {
            Some(ArbitraryInRange::arbitrary_in_range(self.u, self.range))
        } else {
            None
        }
    }
}

/// Utility iterator produced by [`Unstructured::arbitrary_take_rest_iter`]
pub struct ArbitraryTakeRestIter<'a, ElementType> {
    u: Unstructured<'a>,
    _marker: PhantomData<ElementType>,
}

impl<'a, ElementType> ArbitraryTakeRestIter<'a, ElementType> {
    /// Construct a new arbitrary iterator consuming all the remaining bytes.
    pub fn new(u: Unstructured<'a>) -> Self {
        Self {
            u,
            _marker: PhantomData,
        }
    }
}

impl<'a, ElementType: Arbitrary<'a>> Iterator for ArbitraryTakeRestIter<'a, ElementType> {
    type Item = Result<ElementType>;
    fn next(&mut self) -> Option<Result<ElementType>> {
        let keep_going = self.u.arbitrary().unwrap_or(false);
        if keep_going {
            Some(Arbitrary::arbitrary(&mut self.u))
        } else {
            None
        }
    }
}
