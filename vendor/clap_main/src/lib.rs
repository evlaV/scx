use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use quote::quote;
use syn::{parse_macro_input, ItemFn, PatType, Receiver};

#[proc_macro_attribute]
pub fn clap_main(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut f = parse_macro_input!(item as ItemFn);

    // Make sure we actually have a function we can handle
    let item_type = f
        .sig
        .inputs
        .first()
        .expect("Need exactly one argument to the function");

    // Rename the current main function so we can replace it
    let renamed_main = Ident::new("clap_main_fn", Span::call_site());
    f.sig.ident = renamed_main.clone();

    let clap_options_type = match item_type {
        // Match named types since those are the only ones that
        // would have implemented Parser
        syn::FnArg::Receiver(Receiver { ty, .. }) | syn::FnArg::Typed(PatType { ty, .. }) => {
            match ty.as_ref() {
                syn::Type::Path(ty) => ty.path.clone(),
                _ => panic!("Expected a path type"),
            }
        }
    };

    let main_return_type = f.sig.output.clone();

    quote! {
        // Paste the renamed main function here
        #f

        // Set the type so the return value of main gets forwarded
        pub fn main() #main_return_type {
            use clap::Parser;
            use std::io::Write;

            // Handle the error on the type here and only continue
            // if we actually parsed the options. If the user wanted
            // to handle the errors manually they wouldn't be using this
            let args = match #clap_options_type::try_parse() {
                Ok(args) => args,
                Err(e) => {
                    writeln!(&mut std::io::stderr(), "{e}").expect("Could not write to stderr!");
                    // directly exit (we don't care about what possible types main might return
                    // since we are erroring out before it even gets called
                    std::process::exit(-1);
                }
            };

            // Call the decorated main function
            #renamed_main(args)
        }
    }
    .into()
}
