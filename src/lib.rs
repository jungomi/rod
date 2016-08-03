#![cfg_attr(feature="lint", feature(plugin))]
#![cfg_attr(feature="lint", plugin(clippy))]

extern crate syntex_syntax as syntax;
extern crate syntex_pos;
extern crate walkdir;

use std::path::Path;

use walkdir::{DirEntry, WalkDir};

pub mod errors;
pub mod parser;

fn path_contains_hidden(path: &Path) -> bool {
    for component in path.iter() {
        let is_hidden = component.to_str()
            .map_or(false, |s| s.starts_with('.'));
        if is_hidden {
            return true;
        }
    }
    false
}

fn is_rust_file(dir_entry: &DirEntry) -> bool {
    if !dir_entry.file_type().is_file() {
        return false;
    }
    dir_entry.file_name().to_str().map_or(false, |s| s.ends_with(".rs"))
}

fn file_filter(dir_entry: Option<DirEntry>, prefix: &str) -> Option<DirEntry> {
    if let Some(entry) = dir_entry.clone() {
        if !is_rust_file(&entry) {
            return None;
        }
        if let Ok(rest_path) = entry.path().strip_prefix(Path::new(prefix)) {
            if !path_contains_hidden(rest_path) {
                return dir_entry;
            }
        }
    }
    None
}

/// Generates the `rod` documentation of the given file pattern.
///
/// The pattern may be a single file or a directory which will be traversed recursively.
/// Only files with the rust extension `.rs` are considered.
///
/// # Hidden files and directories
///
/// All hidden files and directories are ignored except for the pattern itself.
///
/// Given the following directory structure:
///
/// ```sh
/// $ tree -a
/// .
/// ├── .hidden_dir
/// │   ├── .hidden_in_hidden.rs
/// │   └── visible_in_hidden.rs
/// ├── .hidden_file.rs
/// └── main.rs
/// ```
///
/// - The current directory `.` will only consider `main.rs` because all other files are either
/// hidden or are located in a hidden directory.
/// - To include `.hidden_file.rs` it has to be passed directly.
/// - If the directory `.hidden_dir/` is used, only the `visible_in_hidden.rs` will be considered.
pub fn generate_index(pattern: &str) {
    let walker = WalkDir::new(pattern).into_iter();
    let docs: Vec<_> = walker.filter_map(|e| file_filter(e.ok(), pattern))
        .map(|e| {
            println!("Generating {}", e.path().display());
            let mut doc = parser::FileDoc::with_path(e.path());
            doc.extract_from_file();
            doc
        })
        .collect();
    for doc in docs {
        for func in doc.functions {
            println!("{}", func);
        }
        for st in doc.structs {
            println!("{}", st);
        }
    }
}

pub fn search_pattern(pattern: &str) {
    let _ = pattern;
    unimplemented!();
}
