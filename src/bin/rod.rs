#![cfg_attr(feature="lint", feature(plugin))]
#![cfg_attr(feature="lint", plugin(clippy))]

extern crate clap;
extern crate rod;

use clap::{App, Arg};

fn main() {
    let args = App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .about(env!("CARGO_PKG_DESCRIPTION"))
        .arg(Arg::with_name("generate")
            .help("Generates the rod documentation instead of searching")
            .short("g")
            .long("generate"))
        .arg(Arg::with_name("pattern")
            .help("Pattern to be searched for or the files for which{n}\
                   the rod documentation should be generated")
            .next_line_help(true)
            .multiple(true)
            .required_unless("generate")
            .value_name("PATTERN"))
        .get_matches();

    match (args.is_present("generate"), args.values_of("pattern")) {
        (true, Some(pattern)) => {
            for pat in pattern {
                rod::generate_index(pat)
            }
        }
        (true, None) => rod::generate_index("."),
        (false, Some(pattern)) => rod::search_pattern(&pattern.collect::<Vec<_>>().join(" ")),
        (false, None) => println!("{}", args.usage()),
    }
}
