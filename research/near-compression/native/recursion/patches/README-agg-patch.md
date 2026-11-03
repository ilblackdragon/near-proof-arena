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

## Defect found in D-5 (lane E2E-D, 2026-11-03): program binding of NV children was disabled

In this patch's `nv/verifier.rs` hunk the binding branch reads

    if b.bind || b.bind_child {
        // (comment only)
    } else if false {
        ... the level flag, the anchor check (C_M) and bind_child_program ...
    }

So **no NV child was program-bound** in any tree built from this overlay. Applied to the chain,
it would also have dropped the binding and the level row of every chain level. The production
depth-2/3 aggregation measurements (316 / 322 KB, and the 232,318 vs 232,702 program rows of
`docs/logs/pq-agg-depth2-legal-2026-10-24.md`) were taken with it. The likely reason the branch
was emptied: BIND evaluates the node's own program at the child's batch point through the
reserved E-table, which holds one point. So it cannot serve two children; the multi-child case
failed, and the branch was switched off.

`patches/e2e-tree.patch` (applied on the e2e/zk stack by `setup_e2e_verify_deps.sh` with
`E2E_TREE=1`) carries this overlay rebased and fixed:
* the branch is restored;
* child 0 is bound by BIND;
* every later child is bound by equality of its cached program root with child 0's;
* anchor-level children are bound by the anchor constant or, in the tree, by a pinned anchor set;
* a forced anchor level skips BIND.

This file is kept unchanged as the historical overlay on `f08bf28`. Do not use it for new work.
