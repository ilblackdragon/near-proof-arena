Lock files pinning every dependency used by the build.

* `Cargo.lock` — must be identical to `source/Cargo.lock` (build.sh checks).
* If you vendor crates, `cargo vendor` writes `.cargo-checksum.json` files
  into each vendored crate; those, plus this lock, pin the dependency bytes.
* Lean dependencies are pinned by `formal/lake-manifest.json` and must be in
  the challenge's allowed-package list at the pinned commits.
