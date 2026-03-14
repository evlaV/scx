# Clap Main

This crate provides an procmacro `#[clap_main]` to decorate your entry point function and automatically 
parse a struct that implements clap::Parser from the cli args. 

## Example Usage
Requires clap with the derive feature enabled

```rust

#[derive(clap::Parser)]
struct CliArgs {
  /// A name to be greeted
  name: String
}

#[clap_main::clap_main]
fn main(CliArgs { name }: CliArgs) {
  println!("Hello {name}");  
}
```

