use crate::{size_hint, Arbitrary, Result, Unstructured};

macro_rules! arbitrary_tuple {
    () => {};
    ($last: ident $($xs: ident)*) => {
        arbitrary_tuple!($($xs)*);

        impl<'a, $($xs,)* $last> Arbitrary<'a> for ($($xs,)* $last,)
        where
            $($xs: Arbitrary<'a>,)*
            $last: Arbitrary<'a>,
        {
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                Ok(($($xs::arbitrary(u)?,)* Arbitrary::arbitrary(u)?,))
            }

            #[allow(unused_mut, non_snake_case)]
            fn arbitrary_take_rest(mut u: Unstructured<'a>) -> Result<Self> {
                $(let $xs = $xs::arbitrary(&mut u)?;)*
                let $last = $last::arbitrary_take_rest(u)?;
                Ok(($($xs,)* $last,))
            }

            #[inline]
            fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
                <$last as Arbitrary>::size_hint(context)
                $( + <$xs as Arbitrary>::size_hint(context))*
            }
        }
    };
}
arbitrary_tuple!(A B C D E F G H I J K L M N O P Q R S T U V W X Y Z);
