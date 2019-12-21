use proc_macro2::TokenStream;
use synstructure::*;

decl_derive!([Arbitrary] => arbitrary_derive);

fn arbitrary_derive(s: synstructure::Structure) -> TokenStream {
    if s.variants().len() == 1 {
        // struct
        let con = s.variants()[0].construct(|_, _| quote! { Arbitrary::arbitrary(u)? });
        s.gen_impl(quote! {
            use arbitrary::{Arbitrary, Unstructured};

            gen impl Arbitrary for @Self {
                fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {
                    Ok(#con)
                }
            }
        })
    } else {
        // enum
        let mut variant_tokens = TokenStream::new();

        for (count, variant) in s.variants().iter().enumerate() {
            let count = count as u64;
            let constructor = variant.construct(|_, _| quote! { Arbitrary::arbitrary(u)? });
            variant_tokens.extend(quote! { #count => #constructor, });
        }
        let count = s.variants().len() as u64;
        s.gen_impl(quote! {
            use arbitrary::{Arbitrary, Unstructured};

            gen impl Arbitrary for @Self {
                fn arbitrary<U: Unstructured + ?Sized>(u: &mut U) -> Result<Self, U::Error> {

                    // use multiply + shift to generate a ranged random number
                    // with slight bias
                    // see https://lemire.me/blog/2016/06/30/fast-random-shuffling
                    Ok(match (u64::from(<u32 as Arbitrary>::arbitrary(u)?) * #count) >> 32 {
                        #variant_tokens
                        _ => unreachable!()
                    })
                }
            }
        })
    }
}

#[test]
fn test_arbitrary_struct() {
    test_derive! {
        arbitrary_derive {
            #[derive(Clone)]
            struct ArbitraryTest(u8, bool);
        }
        expands to {
            #[allow(non_upper_case_globals)]
            const _DERIVE_Arbitrary_FOR_ArbitraryTest : () = {
                use arbitrary::{Arbitrary, Unstructured};

                impl Arbitrary for ArbitraryTest {
                    fn arbitrary<U: Unstructured + ?Sized>(u: & mut U) -> Result<Self, U::Error> {
                        Ok(ArbitraryTest(Arbitrary::arbitrary(u)?,
                                         Arbitrary::arbitrary(u)?, ))
                    }
                }
            };
        }
    }
}

#[test]
fn test_arbitrary_enum() {
    test_derive! {
        arbitrary_derive {
            #[derive(Clone)]
            enum ArbitraryTest {
                A,
                B(usize, u32),
                C{ b: bool, d: (u16, u16) }
            }
        }
        expands to {
            #[allow(non_upper_case_globals)]
            const _DERIVE_Arbitrary_FOR_ArbitraryTest : () = {
                use arbitrary::{Arbitrary, Unstructured};

                impl Arbitrary for ArbitraryTest {
                    fn arbitrary<U: Unstructured + ?Sized>(u: & mut U) -> Result<Self, U::Error> {
                        Ok(match (u64::from(<u32 as Arbitrary>::arbitrary(u)?) * 3u64) >> 32 {
                            0u64 => ArbitraryTest::A,
                            1u64 => ArbitraryTest::B(Arbitrary::arbitrary(u)?,
                                                       Arbitrary::arbitrary(u)?,
                                                      ),
                            2u64 => ArbitraryTest::C {
                                    b : Arbitrary::arbitrary(u)?,
                                    d : Arbitrary::arbitrary(u)?,
                                },
                            _ => unreachable!()
                        })
                    }
                }
            };
        }
    }
}
