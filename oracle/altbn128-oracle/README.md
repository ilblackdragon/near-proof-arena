# alt_bn128 reference oracle

A verbatim transcription of nearcore 44f7ae6c (2.13.4, PV86)
`runtime/near-vm-runner/src/logic/alt_bn128.rs` over `zeropool-bn` 0.5.11 — the crate and version
nearcore's own `Cargo.toml:165` pins as `bn = { package = "zeropool-bn", version = "0.5.11",
default-features = false }`. Every decode, curve, subgroup and pairing verdict therefore comes from
the same code nearcore runs, not from a reimplementation.

`wasmtime_runner/logic.rs:932-1053` contributes the argument order, the charge order and the
register write; those are wasm-side plumbing (the Lean side models them from `Wasm/Host.lean`), so
the oracle reproduces the *payload* verdict and the register bytes, and leaves gas to the host-arm
tests.

## Usage

```sh
cargo build --release --offline
./target/release/altbn128-oracle <host> <hexinput> [--raw]
./target/release/altbn128-oracle alt_bn128_pairing_check ''      # -> res 1  (empty product is 1)
```

`<host>` is one of `alt_bn128_g1_multiexp`, `alt_bn128_g1_sum`, `alt_bn128_pairing_check`. Output is
`res <u64>` plus `out <hex>` for the two register writers, or `err <msg>` for an
`AltBn128InvalidInput`/split failure — `msg` matches `logic/alt_bn128.rs`'s formatting, including
Rust's `{:X?}` byte rendering.

## Fixtures

`../gen_altbn128_fixtures.py` builds both corpora from this binary:

* `../fixtures/v3/altbn128/<host>.jsonl` — directed. The 19 vectors of nearcore's own
  `logic/tests/alt_bn128.rs` are parsed mechanically out of the pinned Rust source (balanced-paren
  extraction, so a literal cannot bleed across calls) and the generator asserts the oracle
  reproduces each of nearcore's asserted verdicts; 37 further directed negatives are constructed
  there.
* `../fixtures/v3/altbn128-generated/seed-<n>/<host>.jsonl` — 260 generated comparisons per host per
  seed over four seeds (1,040 per host, 3,120 total).

Verify the oracle against nearcore's own vectors:

```sh
python3 oracle/gen_altbn128_fixtures.py --skip-generated   # regenerates the directed corpus
```
