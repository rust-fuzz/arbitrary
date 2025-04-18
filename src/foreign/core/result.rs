use crate::{Arbitrary, Error, MaxRecursionReached, SizeHint, Unstructured};

impl<'a, T, E> Arbitrary<'a> for Result<T, E>
where
    T: Arbitrary<'a>,
    E: Arbitrary<'a>,
{
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self, Error> {
        Ok(if <bool as Arbitrary<'a>>::arbitrary(u)? {
            Ok(<T as Arbitrary>::arbitrary(u)?)
        } else {
            Err(<E as Arbitrary>::arbitrary(u)?)
        })
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(<bool as Arbitrary>::size_hint(depth)?
            + (<T as Arbitrary>::size_hint(depth)? | <E as Arbitrary>::size_hint(depth)?))
    }
}
