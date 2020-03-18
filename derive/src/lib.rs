extern crate proc_macro;

use proc_macro2::{Literal, TokenStream};
use quote::quote;
use syn::*;

#[proc_macro_derive(Arbitrary)]
pub fn derive_arbitrary(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as syn::DeriveInput);

    let arbitrary_method = gen_arbitrary_method(&input);
    let size_hint_method = gen_size_hint_method(&input);
    let shrink_method = gen_shrink_method(&input);
    let name = input.ident;
    // Add a bound `T: Arbitrary` to every type parameter T.
    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    (quote! {
        impl #impl_generics arbitrary::Arbitrary for #name #ty_generics #where_clause {
            #arbitrary_method
            #size_hint_method
            #shrink_method
        }
    })
    .into()
}

// Add a bound `T: Arbitrary` to every type parameter T.
fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in generics.params.iter_mut() {
        if let GenericParam::Type(type_param) = param {
            type_param.bounds.push(parse_quote!(arbitrary::Arbitrary));
        }
    }
    generics
}

fn gen_arbitrary_method(input: &DeriveInput) -> TokenStream {
    let ident = &input.ident;
    let arbitrary_structlike = |fields| {
        let arbitrary = construct(fields, |_, _| quote!(arbitrary::Arbitrary::arbitrary(u)?));
        let arbitrary_take_rest = construct_take_rest(fields);
        quote! {
            fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
                Ok(#ident #arbitrary)
            }

            fn arbitrary_take_rest(mut u: arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
                Ok(#ident #arbitrary_take_rest)
            }
        }
    };
    match &input.data {
        Data::Struct(data) => arbitrary_structlike(&data.fields),
        Data::Union(data) => arbitrary_structlike(&Fields::Named(data.fields.clone())),
        Data::Enum(data) => {
            let variants = data.variants.iter().enumerate().map(|(i, variant)| {
                let idx = i as u64;
                let ctor = construct(&variant.fields, |_, _| {
                    quote!(arbitrary::Arbitrary::arbitrary(u)?)
                });
                let variant_name = &variant.ident;
                quote! { #idx => #ident::#variant_name #ctor }
            });
            let variants_take_rest = data.variants.iter().enumerate().map(|(i, variant)| {
                let idx = i as u64;
                let ctor = construct_take_rest(&variant.fields);
                let variant_name = &variant.ident;
                quote! { #idx => #ident::#variant_name #ctor }
            });
            let count = data.variants.len() as u64;
            quote! {
                fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
                    // Use a multiply + shift to generate a ranged random number
                    // with slight bias. For details, see:
                    // https://lemire.me/blog/2016/06/30/fast-random-shuffling
                    Ok(match (u64::from(<u32 as arbitrary::Arbitrary>::arbitrary(u)?) * #count) >> 32 {
                        #(#variants,)*
                        _ => unreachable!()
                    })
                }

                fn arbitrary_take_rest(mut u: arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
                    // Use a multiply + shift to generate a ranged random number
                    // with slight bias. For details, see:
                    // https://lemire.me/blog/2016/06/30/fast-random-shuffling
                    Ok(match (u64::from(<u32 as arbitrary::Arbitrary>::arbitrary(&mut u)?) * #count) >> 32 {
                        #(#variants_take_rest,)*
                        _ => unreachable!()
                    })
                }
            }
        }
    }
}

fn construct(fields: &Fields, ctor: impl Fn(usize, &Field) -> TokenStream) -> TokenStream {
    match fields {
        Fields::Named(names) => {
            let names = names.named.iter().enumerate().map(|(i, f)| {
                let name = f.ident.as_ref().unwrap();
                let ctor = ctor(i, f);
                quote! { #name: #ctor }
            });
            quote! { { #(#names,)* } }
        }
        Fields::Unnamed(names) => {
            let names = names.unnamed.iter().enumerate().map(|(i, f)| {
                let ctor = ctor(i, f);
                quote! { #ctor }
            });
            quote! { ( #(#names),* ) }
        }
        Fields::Unit => quote!(),
    }
}

fn construct_take_rest(fields: &Fields) -> TokenStream {
    construct(fields, |idx, _| {
        if idx + 1 == fields.len() {
            quote! { arbitrary::Arbitrary::arbitrary_take_rest(u)? }
        } else {
            quote! { arbitrary::Arbitrary::arbitrary(&mut u)? }
        }
    })
}

fn gen_size_hint_method(input: &DeriveInput) -> TokenStream {
    let size_hint_fields = |fields: &Fields| {
        let tys = fields.iter().map(|f| &f.ty);
        quote! {
            arbitrary::size_hint::and_all(&[
                #( <#tys as Arbitrary>::size_hint(depth) ),*
            ])
        }
    };
    let size_hint_structlike = |fields: &Fields| {
        let hint = size_hint_fields(fields);
        quote! {
            #[inline]
            fn size_hint(depth: usize) -> (usize, Option<usize>) {
                arbitrary::size_hint::recursion_guard(depth, |depth| #hint)
            }
        }
    };
    match &input.data {
        Data::Struct(data) => size_hint_structlike(&data.fields),
        Data::Union(data) => size_hint_structlike(&Fields::Named(data.fields.clone())),
        Data::Enum(data) => {
            let variants = data.variants.iter().map(|v| size_hint_fields(&v.fields));
            quote! {
                #[inline]
                fn size_hint(depth: usize) -> (usize, Option<usize>) {
                    arbitrary::size_hint::and(
                        <u32 as Arbitrary>::size_hint(depth),
                        arbitrary::size_hint::recursion_guard(depth, |depth| {
                            arbitrary::size_hint::or_all(&[ #( #variants ),* ])
                        }),
                    )
                }
            }
        }
    }
}

fn gen_shrink_method(input: &DeriveInput) -> TokenStream {
    let ident = &input.ident;
    let shrink_structlike = |fields| {
        let inner = shrink(&quote!(#ident), fields, |i, field| match &field.ident {
            Some(i) => quote!(&self.#i),
            None => {
                let i = Literal::usize_unsuffixed(i);
                quote!(&self.#i)
            }
        });
        quote! {
            fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                #inner
            }
        }
    };

    return match &input.data {
        Data::Struct(data) => shrink_structlike(&data.fields),
        Data::Union(data) => shrink_structlike(&Fields::Named(data.fields.clone())),
        Data::Enum(data) => {
            let variants = data.variants.iter().map(|variant| {
                let mut binding_names = Vec::new();
                let bindings = match &variant.fields {
                    Fields::Named(_) => {
                        let names = variant.fields.iter().map(|f| {
                            let name = f.ident.as_ref().unwrap();
                            binding_names.push(quote!(#name));
                            name
                        });
                        quote!({#(#names),*})
                    }
                    Fields::Unnamed(_) => {
                        let names = (0..variant.fields.len()).map(|i| {
                            let name = quote::format_ident!("f{}", i);
                            binding_names.push(quote!(#name));
                            name
                        });
                        quote!((#(#names),*))
                    }
                    Fields::Unit => quote!(),
                };
                let variant_name = &variant.ident;
                let shrink = shrink(&quote!(#ident::#variant_name), &variant.fields, |i, _| {
                    binding_names[i].clone()
                });
                quote!(#ident::#variant_name #bindings => { #shrink })
            });
            quote! {
                fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                    match self {
                        #(#variants)*
                    }
                }
            }
        }
    };

    fn shrink(
        prefix: &TokenStream,
        fields: &Fields,
        access_field: impl Fn(usize, &Field) -> TokenStream,
    ) -> TokenStream {
        if fields.len() == 0 {
            return quote!(Box::new(None.into_iter()));
        }
        let iters = fields.iter().enumerate().map(|(i, f)| {
            let name = quote::format_ident!("field{}", i);
            let field = access_field(i, f);
            quote! { let mut #name = arbitrary::Arbitrary::shrink(#field); }
        });
        let ctor = construct(fields, |i, _| {
            let iter = quote::format_ident!("field{}", i);
            quote!(#iter.next()?)
        });
        quote! {
                #(#iters)*
                Box::new(std::iter::from_fn(move || {
                    Some(#prefix #ctor)
                }))
        }
    }
}
