//! Judge-side sandbox helper (`shim` on the host, `init` inside bwrap).
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    std::process::exit(arena_sandbox::helper::helper_main(&args));
}
