//! Macro definitions used to maintain the crate
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use std::collections::HashMap;
use syn::__private::TokenStream2;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Attribute, Expr, Item, Lit, Meta, Token};

struct ParsedStruct {
    attrs: Vec<Attribute>,
}

impl Parse for ParsedStruct {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(ParsedStruct {
            attrs: input.call(Attribute::parse_inner)?,
        })
    }
}

/// Allow to compute the range of supported api versions for a functionality.
///
/// This macro came out from the frustration of bumping fdb's version, where
/// we are spending most of our time searching for things like:
/// `#[cfg(any(feature = "fdb-5_1", feature = "fdb-5_2", feature = "fdb-6_0"))]`
/// and adding the new version manually.
///
/// Thanks to the macro, we can now specify a `minimum` and an optional `max` version, and
/// generate the right list of any. Not specifying a `max` allow easy bump to a new version.
///
/// `#[cfg_api_versions(min = 510, max = 600)]` will be translated to:
/// `#[cfg(any(feature = "fdb-5_1", feature = "fdb-5_2", feature = "fdb-6_0"))]`
#[proc_macro_attribute]
pub fn cfg_api_versions(attr: TokenStream, item: TokenStream) -> TokenStream {
    cfg_api_versions_internal(attr, item)
}

fn cfg_api_versions_internal(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as Item);
    let attributes = syn::parse_macro_input!(attr as ParsedStruct);

    let (minimum_version, maximum_version) = parse_version_arguments(attributes.attrs);
    generate_feature_range(&input, minimum_version, maximum_version)
}

/// Search for a required min and an optional max in the attributes
fn parse_version_arguments(attributes_args: Vec<Attribute>) -> (i32, Option<i32>) {
    let min = attributes_args
        .iter()
        .find_map(|attribute| find_attribute(attribute, "min"))
        .expect("Macro is expecting at least a 'min' argument");

    let max = attributes_args
        .iter()
        .find_map(|attribute| find_attribute(attribute, "max"));

    (min, max)
}

/// given an attribute's key, returns the associated i32, or None.
fn find_attribute(attribute: &Attribute, key: &str) -> Option<i32> {
    if attribute.path().is_ident("cfg_api_versions") {
        let nested = attribute
            .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
            .expect("cannot parse nested argument in procedure macro");
        for meta in nested {
            if let Meta::NameValue(name_value) = meta {
                if name_value.path.is_ident(key) {
                    if let Expr::Lit(attribute_expr) = &name_value.value {
                        if let Lit::Int(attribute_value) = &attribute_expr.lit {
                            return Some(
                                attribute_value
                                    .base10_parse::<i32>()
                                    .expect("could not cast attribute to i32"),
                            );
                        }
                    }
                }
            }
        }
    }
    None
}

fn generate_feature_range(
    input: &Item,
    minimum_version: i32,
    maximum_version: Option<i32>,
) -> TokenStream {
    let allowed_fdb_versions: Vec<TokenStream2> =
        get_supported_feature_range(minimum_version, maximum_version)
            .iter()
            .map(|fdb_version| quote!(feature = #fdb_version))
            .collect();

    let result = quote!(
        #[cfg(any(#(#allowed_fdb_versions),*))]
        #input
    );

    result.into()
}

/// Given a range of version, this function will generate the appropriate macro text.
fn get_supported_feature_range(minimum_version: i32, maximum_version: Option<i32>) -> Vec<String> {
    let mut values: Vec<String> = get_version_mapping()
        .iter()
        .filter(|(_, version)| match maximum_version {
            None => minimum_version <= **version,
            Some(maximum) => minimum_version <= **version && version <= &&maximum,
        })
        .map(|(feature, _)| feature.to_owned())
        .collect();
    values.sort();

    values
}

// TODO: Should we import something like lazy_static?
fn get_version_mapping() -> HashMap<String, i32> {
    let mut version_mapping = HashMap::with_capacity(8);
    version_mapping.insert("fdb-7_1".into(), 710);
    version_mapping.insert("fdb-7_0".into(), 700);
    version_mapping.insert("fdb-6_3".into(), 630);
    version_mapping.insert("fdb-6_2".into(), 620);
    version_mapping.insert("fdb-6_1".into(), 610);
    version_mapping.insert("fdb-6_0".into(), 600);
    version_mapping.insert("fdb-5_2".into(), 520);
    version_mapping.insert("fdb-5_1".into(), 510);
    version_mapping.insert("fdb-5_0".into(), 500);
    version_mapping
}

#[cfg(test)]
mod tests {
    use crate::{get_supported_feature_range, parse_version_arguments};
    use syn::{parse_quote, Attribute};

    #[test]
    fn test_create_supported_list() {
        let v = get_supported_feature_range(700, None);
        assert_eq!(v.len(), 2);
        assert!(v.contains(&String::from("fdb-7_0")));
        assert!(v.contains(&String::from("fdb-7_1")));

        let v = get_supported_feature_range(600, Some(700));
        assert_eq!(v.len(), 5);
        assert!(v.contains(&String::from("fdb-7_0")));
        assert!(v.contains(&String::from("fdb-6_3")));
        assert!(v.contains(&String::from("fdb-6_2")));
        assert!(v.contains(&String::from("fdb-6_1")));
        assert!(v.contains(&String::from("fdb-6_0")));

        let v = get_supported_feature_range(500, Some(610));
        assert_eq!(v.len(), 5);
        assert!(v.contains(&String::from("fdb-6_1")));
        assert!(v.contains(&String::from("fdb-6_0")));
        assert!(v.contains(&String::from("fdb-5_2")));
        assert!(v.contains(&String::from("fdb-5_1")));
        assert!(v.contains(&String::from("fdb-5_0")));

        let v = get_supported_feature_range(500, None);
        assert_eq!(v.len(), 9);
        assert!(v.contains(&String::from("fdb-7_1")));
        assert!(v.contains(&String::from("fdb-7_0")));
        assert!(v.contains(&String::from("fdb-6_3")));
        assert!(v.contains(&String::from("fdb-6_2")));
        assert!(v.contains(&String::from("fdb-6_1")));
        assert!(v.contains(&String::from("fdb-6_0")));
        assert!(v.contains(&String::from("fdb-5_2")));
        assert!(v.contains(&String::from("fdb-5_1")));
        assert!(v.contains(&String::from("fdb-5_0")));
    }

    #[test]
    fn test_version_extract_no_max() {
        let attr: Attribute = parse_quote! {
            #[cfg_api_versions(min = 620)]
        };

        let result = parse_version_arguments(vec![attr]);
        assert_eq!(result, (620, None));
    }

    #[test]
    fn test_version_extract_with_max() {
        let attr: Attribute = parse_quote! {
            #[cfg_api_versions(min = 620, max = 700)]
        };

        let result = parse_version_arguments(vec![attr]);
        assert_eq!(result, (620, Some(700)));
    }
}
