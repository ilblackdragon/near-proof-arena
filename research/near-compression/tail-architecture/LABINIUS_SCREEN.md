# Binary/lattice candidate: measured component screen

New candidate priority: a binary-field PIOP with a compact lattice opening,
combined with sparse/interval receipt semantics. This changes assumptions from
the SHA384-only baseline; no signed challenge, verifier policy or production
parameters are changed by this experiment.

Upstream: [LaBinius implementation](https://github.com/osdnk/labinius), commit
`96b57f724fc15c8e40495015c01dc3e6d8dfe595`;
[preprint](https://eprint.iacr.org/2026/2103). Source uses a lattice commitment
and binary-field evaluation, with a LaBRADOR opening compressor. The repository
provides Binius hash circuits; it is not a complete NEAR proof system.

## Native commitment/opening measurements

One AMD 9950X3D core (CPU 8), native AVX-512, upstream's ten repetitions per stage,
warm reusable workspaces. Totals below sum stage medians; not cold end-to-end
medians. Other CPU-heavy work was present on the machine.

| Binary witness payload | Commit + opening | Verify | Analytical size | Peak RSS |
|---|---:|---:|---:|---:|
| 21,233,664 B | 499 ms | 242 ms | 76.7 KiB | 847 MB |
| 84,934,656 B | 1,181 ms | 540 ms | 90.2 KiB | 2,358 MB |

Random native F162 witnesses; excludes witness generation and reusable setup.
Upstream `opening` tests: **11 passed**, including wrong norms, changed left
commitment, other witness commitments and wrong challenge sets.

## Private SHA-256 experiment

Added a private-message constructor to the upstream circuit: message wires become
witness wires; digest wires remain public. Original SHA gadget and constraints
remain. Tested one synthetic 65,536-byte message, **1,025 SHA-256 compressions**.

Three proofs, each verified in-process and subjected to three negative checks:
changed public digest words, a changed transcript byte, and a changed norm claim.
All honest verifications accepted; all nine negatives rejected.

- Median witness + prove: **194.2 ms** (witness generation ~2.7 ms).
- Median verify: **96.6 ms**.
- Analytical proof size: **97,745 B**, plus **64 B public digest word encoding**.
- Actual Binius transcript portion: **20,537 B**; opening remains an opaque handle.
- Circuit construction: **812 ms**; reusable session/key setup: **152 ms**.
- First witness + proof: **210 ms**. Circuit/key setup is reusable only for the
  tested fixed circuit shape, not automatically arbitrary NEAR message batches.

The unchanged upstream public-message SHA benchmark also passed: 1,134
compressions, 197 ms proving, reported canonical analytical size 88.89 KiB.
That public-message benchmark is not a private receipt-hashing relation.

## Size and security qualification

**No complete serialized recursive proof was measured.**
`crates/pcs/src/labrador/mod.rs::ProofHandle` contains opaque C pointers and an
analytical `size_kb`; `OpeningProof::wire_bytes` includes that estimate. The
Binius integration explicitly documents that recursive openings have no byte
form. A lower reported analytical size is evidence for engineering exploration,
not a passed 300,000-byte artifact gate. The benchmark omits a few statement
bytes in some totals; use complete canonical packet accounting when implemented.

**No concrete PQ128 security claim is established here.** In addition to the
lattice assumptions, audit reduction losses, norms, folding challenges and FS
composition. Upstream `sis_secure` uses a fixed root-Hermite-factor rule
(`LOGDELTA = log2(1.00444)`). The C backend contains 16-byte transcript chaining
values and SHAKE128/AES128 paths; the outer transcript uses BLAKE3. These choices
require an explicit concrete quantum-security analysis. Passing mutations does
not certify them. The compressor's internal recursion is not recursion over NEAR
chunk proofs.

## Connection to the interval experiment

Our large receipt trace has 1,955,262 nonzero intervals; 1,785,850 are singletons.
There are 236,802 distinct ranges and 156,411 distinct endpoint positions. Naively
committing random extension-field lookup results could erase the storage savings.

[Twist and Shout / Spark++](https://people.cs.georgetown.edu/jthaler/TwistShout.pdf)
provides a sparse-evaluation construction that keeps lookup results virtual.
Its PIOP is a candidate for the interval opening argument; hash-based commitment
choices are discussed in the paper. This suggests paying for packed address bits
rather than a dense field vector. It does **not** justify importing curve-based
Jolt security or performance numbers into this candidate.

## Next acceptance gates

1. Extract the actual NEAR SHA message batch from `case_inputs.entries["sha_r"]`,
   prove the correct independent hash calls, and bind message identifiers, lengths,
   bytes and digests to receipt constraints. One long hash is not that relation.
2. Implement and audit canonical recursive-opening serialization; verify a fresh
   process using only the packet, expected claim and fixed verifier configuration.
   Count public data and any circuit/setup selectors; reject all parser mutations.
3. Audit concrete PQ security and determine parameter changes before claiming a
   secure-size result. Keep lattice assumptions explicit.
4. Build the authenticated sparse/interval opening and bus/constraint argument.
   Measure the total witness, hash, receipt and aggregation pipeline against the
   **1–2 s / <300,000 B** goal on representative NEAR cases, including the large
   receipt workload. Full Wasm/state semantics and chunk recursion remain required.

## Reproduce

Scratch checkout: `/data/illia/pq-tail-architecture-20261024/labinius`.
Workspace patch retains only pcs/bench/binius members to avoid unrelated builds.
Private-message patch and original benchmark logs are in `evidence/labinius/`.
Copy `near_sha_screen.rs` to `crates/binius/src/bin/near-sha-screen.rs` after applying
`private-message.patch`. Compile with explicit
`RUSTFLAGS='-C target-cpu=native -C link-arg=-fuse-ld=mold'`: global Cargo target
configuration otherwise overrides the project's native setting and AVX-512 fails.

```
cargo build --release -p labinius-bench --features labrador --bin labinius
BENCH_CPU=8 target/release/labinius --suite m
BENCH_CPU=8 target/release/labinius --suite l
cargo test --release -p labinius --features labrador --test opening -- --test-threads=1
cargo build --release -p labinius-binius --bin near-sha-screen
BENCH_CPU=8 target/release/near-sha-screen
```

`collect_labinius.py` pins upstream revision, binaries, manifests and logs. The
private SHA evidence pins its extra source and binary. Proof objects are currently
process-local, not portable artifacts. No claimed goal completion.
