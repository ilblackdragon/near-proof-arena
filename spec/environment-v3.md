# Environment assumptions of the v3 chunk-validation package

Workplan item 12. This file and its machine-readable form [`environment-v3.json`](environment-v3.json)
are part of the frozen package: they state the validator environment under which the package's
agreement claims ("Lean accepts ⇔ pinned nearcore accepts") are made. They do not change any claim,
witness or relation; a claim and a witness are the same bytes whatever the environment.

Pinned nearcore 2.13.4 = `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol version 86, mainnet
parameters. Paths below are in that tree unless stated; `W45` is the `wasmtime-45.0.0` crate.

## ENV-1 Reference validator: x86_64, Wasmtime 45.0.0 with Winch

The reference is the pinned validator built for **x86_64**, which compiles contracts with
**Winch** (`runtime/near-vm-runner/src/wasmtime_runner/mod.rs:512-521`:
`if cfg!(target_arch = "x86_64") { Strategy::Winch } else { Strategy::Cranelift }`, commented
"Winch on x86_64 (production); Cranelift elsewhere (e.g. aarch64 development environment)"), with
the engine configuration of `mod.rs:455-545` (pooling allocator for `MAX_CONCURRENCY = 1000`
instances, `cranelift_nan_canonicalization(true)`, …). Every fixture, corpus verdict and
instance-layout boundary in the evidence was produced by this build.

## ENV-2 Host state is healthy (from UQ-014)

Assumed absent on the validating node (evidence:
[runtime-errors §2](../docs/evidence/lean-chunk-completion/runtime-errors/README.md)):

* execution-slot exhaustion (`failed to acquire execution slot`, `mod.rs:1012-1018`, `try_acquire`
  `:230-269`);
* instantiation failures from host resources: pool slots, memory-image mapping, `mmap`/`mprotect`,
  fallible allocation (`mod.rs:1019-1026`, `W45/runtime/module.rs:528-533, 545`);
* compiled-contract cache I/O errors and cache entries this engine did not write (a foreign or
  corrupted artifact: `cache.rs:55-67, 820-848`, `mod.rs:654-675`).

In words: the process has the memory, address space and file system its configuration requires,
and its compiled-contract cache holds only entries this engine wrote. These are conditions on node
operation, not on chunk content, and no relation over `(claim, witness)` can check them. If one
fails on a validator, any outcome that differs from Lean's also differs from the chunk header, so
that validator fails `validate_chunk_with_chunk_extra_and_receipts_root`
(`chain/chain/src/stateless_validation/chunk_validation.rs:755`) and does not endorse; no host
condition turns a chunk Lean rejects into one nearcore accepts.

## ENV-3 Architectures

| architecture | status | basis |
|---|---|---|
| x86_64 (Winch) | **reference** | ENV-1; all evidence |
| aarch64 (Cranelift) | **excluded from the reference by this statement** | measured partially, below |
| others | excluded | not built or measured |

aarch64 was measured under emulation (QEMU 8.2.2 user mode, a static `aarch64-unknown-linux-musl`
build of the same `wasmtime = 45.0.0` with nearcore's engine configuration,
`tools/instance-layout/`; evidence:
[open-uqs/README.md §item 12](../docs/evidence/lean-chunk-completion/open-uqs/README.md)):

* **instance layout** (the UQ-014 `LoadingError` boundary): the largest fitting global count is
  65,501 / 65,344 / 65,505 for the three module shapes, **equal** to x86_64 and to the pinned
  harness (`runtime-errors/boundary.json`);
* **floats and NaNs** (UQ-003): 5,920 operator calls over signed/payload NaNs, infinities, signed
  zeros, subnormals and extremes give **bit-identical** results on aarch64/Cranelift, x86_64/Winch
  and the Lean float kernel; every NaN result of a canonicalising operator is the positive
  canonical NaN.

Not measured on aarch64, hence the exclusion: the other Winch/Cranelift differences (trap
classification, native stack use and compile-time limits, hazard H11 in
`docs/research/near-wasm-boundary.md`), real silicon (only emulation was used), and whole-chunk
replays. An aarch64 validator is expected to agree, but the package makes no claim about it.

## ENV-4 Cache and code environment

Ground truth is the pinned validator run **cold** (empty compiled-contract cache at the start of the
chunk). The cache statement itself is UQ-001 (owned elsewhere); the named out-of-domain reasons that
come from the environment are the preparation-pipeline thread race (`e.wasm-α … pipelined before the
in-chunk deploy`) and a cold code fetch above the 64 MiB response cap (`w.code_response_size`).
