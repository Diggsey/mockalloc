#![deny(missing_docs)]
//! mockalloc-macros
//!
//! Provides the `#[mockalloc::test]` procedural macro for the `mockalloc`
//! crate.

use proc_macro::TokenStream;
use quote::quote;

/// Replacement for the `#[test]` macro to automatically detect allocation
/// bugs from within the test.
///
/// Equivalent to wrapping the test body in
/// `mockalloc::assert_allocs(|| { ... });`.
#[proc_macro_attribute]
pub fn test(_args: TokenStream, item: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(item as syn::ItemFn);
    let sig = &input.sig;
    let body = &input.block;
    let attrs = &input.attrs;
    let vis = input.vis;

    let result = quote! {
        #[::core::prelude::v1::test]
        #(#attrs)*
        #vis #sig {
            ::mockalloc::assert_allocs(move || {
                #body
            });
        }
    };

    result.into()
}
