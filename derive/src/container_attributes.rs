use crate::ARBITRARY_ATTRIBUTE_NAME;
use quote::ToTokens;
use syn::{
    parse::Error, punctuated::Punctuated, DeriveInput, Lit, Meta, MetaNameValue, NestedMeta, Token,
    TypeParam,
};

pub struct ContainerAttributes {
    pub bounds: Option<Vec<Punctuated<TypeParam, Token![,]>>>,
}

impl ContainerAttributes {
    pub fn from_derive_input(derive_input: &DeriveInput) -> Result<Self, Error> {
        let mut bounds = None;

        for attr in &derive_input.attrs {
            if !attr.path.is_ident(ARBITRARY_ATTRIBUTE_NAME) {
                continue;
            }

            let meta_list = match attr.parse_meta()? {
                Meta::List(l) => l,
                _ => panic!(
                    "invalid `{}` attribute. expected list",
                    ARBITRARY_ATTRIBUTE_NAME
                ),
            };

            for nested_meta in meta_list.nested.iter() {
                match nested_meta {
                    NestedMeta::Meta(Meta::NameValue(MetaNameValue {
                        path,
                        lit: Lit::Str(bound_str_lit),
                        ..
                    })) if path.is_ident("bound") => {
                        bounds
                            .get_or_insert_with(Vec::new)
                            .push(bound_str_lit.parse_with(Punctuated::parse_terminated)?);
                    }
                    _ => panic!(
                        "invalid value for `{}` attribute. expected `bound = \"..\"`, got: `{}`",
                        ARBITRARY_ATTRIBUTE_NAME,
                        nested_meta.to_token_stream()
                    ),
                }
            }
        }

        Ok(Self { bounds })
    }
}
