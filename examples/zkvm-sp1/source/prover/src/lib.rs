//! Shared host-side helpers for prepare/prove.
use sp1_sdk::Elf;

/// The guest program, built by build-recipe/build.sh before the host crates.
pub const GUEST_ELF: Elf =
    Elf::Static(include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../guest-elf/transfer-guest.elf")));

pub fn die(code: i32, msg: impl std::fmt::Display) -> ! {
    eprintln!("{msg}");
    std::process::exit(code)
}
