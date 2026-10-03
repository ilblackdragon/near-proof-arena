//! Print the CONTRACTS §1 TreeDigest (`arena_archive::tree_from_dir`) of a
//! directory. Used to name toolchain images (`<images_dir>/<hex>`).
//!
//! `arena-tree-digest DIR` -> `sha256:<hex> <files> <bytes>`

fn main() {
    let Some(dir) = std::env::args().nth(1) else {
        eprintln!("usage: arena-tree-digest DIR");
        std::process::exit(2);
    };
    let lim = arena_archive::Limits {
        max_expanded_bytes: 64 << 30,
        max_entries: 5_000_000,
        ..Default::default()
    };
    match arena_archive::tree_from_dir(std::path::Path::new(&dir), &lim) {
        Ok(t) => {
            let bytes: u64 = t.files.values().map(|f| f.size).sum();
            println!("{} {} {}", t.digest(), t.files.len(), bytes);
        }
        Err(e) => {
            eprintln!("{dir}: {e}");
            std::process::exit(1);
        }
    }
}
