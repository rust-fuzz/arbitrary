use proc_macro2::{Ident, Span, TokenStream};
use synstructure::*;

decl_derive!([Arbitrary] => arbitrary_derive);

fn gen_arbitrary_method(variants: &[VariantInfo]) -> TokenStream {
    if variants.len() == 1 {
        // struct
        let con = variants[0].construct(|_, _| quote! { Arbitrary::arbitrary(u)? });
        quote! {
            fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
                Ok(#con)
            }
        }
    } else {
        // enum
        let mut variant_tokens = TokenStream::new();

        for (count, variant) in variants.iter().enumerate() {
            let count = count as u64;
            let constructor = variant.construct(|_, _| quote! { Arbitrary::arbitrary(u)? });
            variant_tokens.extend(quote! { #count => #constructor, });
        }

        let count = variants.len() as u64;

        quote! {
            fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
                // Use a multiply + shift to generate a ranged random number
                // with slight bias. For details, see:
                // https://lemire.me/blog/2016/06/30/fast-random-shuffling
                Ok(match (u64::from(<u32 as Arbitrary>::arbitrary(u)?) * #count) >> 32 {
                    #variant_tokens
                    _ => unreachable!()
                })
            }
        }
    }
}

fn gen_size_hint_method(s: &Structure) -> TokenStream {
    let mut sizes = Vec::with_capacity(s.variants().len());
    for v in s.variants().iter() {
        let tys = v.ast().fields.iter().map(|f| &f.ty);
        sizes.push(quote! {
            arbitrary::size_hint::and_all(&[
                #( <#tys as Arbitrary>::size_hint() ),*
            ])
        });
    }
    quote! {
        fn size_hint() -> (usize, Option<usize>) {
            arbitrary::size_hint::or_all(&[ #( #sizes ),* ])
        }
    }
}

fn gen_shrink_method(s: &Structure) -> TokenStream {
    let variants = s.each_variant(|v| {
        if v.bindings().is_empty() {
            return quote! {
                Box::new(None.into_iter())
            };
        }

        let mut value_idents = vec![];
        let mut shrinker_idents = vec![];
        let mut shrinker_exprs = vec![];
        for (i, b) in v.bindings().iter().enumerate() {
            value_idents.push(Ident::new(&format!("value{}", i), Span::call_site()));
            shrinker_idents.push(Ident::new(&format!("shrinker{}", i), Span::call_site()));
            shrinker_exprs.push(quote! { Arbitrary::shrink(#b) });
        }
        let cons = v.construct(|_, i| &value_idents[i]);
        let shrinker_idents = &shrinker_idents;
        quote! {
            #( let mut #shrinker_idents = #shrinker_exprs; )*
            Box::new(std::iter::from_fn(move || {
                #( let #value_idents = #shrinker_idents.next()?; )*
                Some(#cons)
            }))
        }
    });

    quote! {
        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            match self {
                #variants
            }
        }
    }
}

fn arbitrary_derive(s: Structure) -> TokenStream {
    let arbitrary_method = gen_arbitrary_method(s.variants());
    let size_hint_method = gen_size_hint_method(&s);
    let shrink_method = gen_shrink_method(&s);
    s.gen_impl(quote! {
        use arbitrary::{Arbitrary, Unstructured, Result};
        gen impl Arbitrary for @Self {
            #arbitrary_method
            #size_hint_method
            #shrink_method
        }
    })
}
