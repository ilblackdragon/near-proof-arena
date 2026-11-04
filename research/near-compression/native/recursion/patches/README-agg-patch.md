# openvm-recursion-agg.patch — provenance (2026-10-23)

## What this patch is
The aggregation-node overlay (`crates/recursion/src/nv/agg.rs` plus its wiring into
`builder.rs`, `circuit.rs`, `glue.rs`, `isa.rs`, `mod.rs`, `tests.rs`, `transcript2.rs`,
`uair.rs`, `verifier.rs`, and `sha384/config.rs`). Applied on top of
`openvm-recursion-sha384.patch` in a pristine `openvm-sha384` checkout at commit `f08bf28`.

## Why it was regenerated
The previous copy (`openvm-recursion-agg.patch.bak-20261021`, 64,596 B, 12 files) no longer
applies. `git apply` fails on 8 of its 12 files:

    error: patch failed: crates/recursion/src/nv/builder.rs:142
    error: patch failed: crates/recursion/src/nv/circuit.rs:150
    error: patch failed: crates/recursion/src/nv/glue.rs:501
    error: patch failed: crates/recursion/src/nv/isa.rs:75
    error: patch failed: crates/recursion/src/nv/mod.rs:9
    error: patch failed: crates/recursion/src/nv/tests.rs:93
    error: patch failed: crates/recursion/src/nv/transcript2.rs:364
    error: patch failed: crates/recursion/src/nv/uair.rs:134
    error: patch failed: crates/recursion/src/nv/verifier.rs:357
    error: patch failed: crates/recursion/src/sha384/config.rs:43

The cause is ordering, not bit-rot: `openvm-recursion-sha384.patch` moved forward (it now adds
`nv/faithful_dof.rs`, `nv/faithful_sha_tests.rs`, `nv/faithful_tests.rs`,
`nv/faithful_tr_tests.rs`, `sha384/compress4_air.rs`, `sha384/compress4_trace.rs`, which the
canonical `pq-base-agg` overlay tree does not have), and the agg patch was never rebased on top
of the new base. So the base patch is *newer* than the canonical overlay, and the agg patch is
older than both.

## How it was regenerated (reproducible)
1. Clone `openvm-sha384`, `git checkout --detach f08bf28`.
2. `git apply patches/openvm-recursion-sha384.patch` (rc=0), `git add -N .`.
3. Copy the 12 agg files from `/data/illia/nearproof-deps/pq-agg/openvm-sha384` over the tree.
4. `git diff HEAD > openvm-recursion-agg.patch`.

Verified: a fresh clone + base patch + this patch reproduces **all 12 files byte-identically**
against `pq-agg/openvm-sha384` (`cmp` on `agg.rs`, `agg_tests.rs`, `builder.rs`, `circuit.rs`,
`verifier.rs`, `sha384/config.rs` all SAME; full `diff -rq` leaves zero differences in those 12).

## Deliberately excluded
Three files in the production tree are **not** in this patch because they belong to other lanes,
not the aggregation work:

| file | lane |
|---|---|
| `crates/recursion/src/nv/stream_tests.rs` | stream research |
| `crates/recursion/src/sha384/mb.rs` | pq-cpu-prover (multi-buffer SHA-384) |
| `crates/recursion/src/sha384/mod.rs` | the `mod mb;` registration for the above |

So a tree built from base + this patch alone will **not** be byte-identical to
`pq-agg/openvm-sha384`; it will differ by exactly those three files. The aggregation code
itself — including `agg.rs`, `agg_tests.rs`, and every `build_agg`/`ChildKind`/`RangeStmt`
wiring — is reproduced exactly. A run that needs `stream_tests.rs` or `mb.rs` must also apply
those lanes' overlays.
