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
