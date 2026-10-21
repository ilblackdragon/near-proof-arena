# Refreshing the PQ dependency trees (2026-10-21)

Context: after merging `fix/pq-paper-soundness` and `lane/pq-nv-faithful`, every
`$NEARPROOF_PQ_DEPS/<lane>/stark-backend-unified` tree on this host had drifted
from `patches/stark-backend-unified.patch`. They still compiled — the code the
crate happens to use was unchanged — so the drift was invisible until a setup
script was run. `docs/HANDOVER.md` rule 6 records the trap.

None of `pq-recursion`, `pq-stream-g2`, `pq-cpu2` are git branches. The three
*lane* branches (`lane/pq-recursion-sha384`, `lane/pq-stream-commit`,
`lane/pq-cpu-prover`) were already merged into `main` before this refresh; what
was stale is the dependency state those lanes' scripts reproduce from.

## What each tree is

| tree | stack | verifier |
|---|---|---|
| `pq-recursion` | native → unified → `openvm-recursion-sha384` | `setup_recursion_deps.sh` |
| `pq-stream-g2` | + stream → + cpu-fast | `setup_cpu_fast_deps.sh` |
| `pq-cpu2` | + stream → + cpu-fast | `setup_cpu_fast_deps.sh` |

`pq-recursion` is the recursion-only lane, so `setup_cpu_fast_deps.sh` correctly
*fails* on it (no overlay markers). That is expected, not a defect.

## Refresh procedure

The setup scripts verify-or-refuse for an existing tree; they never re-patch. So
a refresh is reset-to-pristine then re-apply the stack, then let the governing
script verify:

```
cd $DEPS/<component>
git reset -q && git checkout -- . && git clean -qfd      # intent-to-add needs reset
git apply <each patch in stack order>
git add -N .        # so `git diff HEAD` reproduces the patch for the verifier
```

Two traps found:

1. `git checkout -- .` alone does **not** undo `git add -N` files. Without
   `git reset -q && git clean -qfd` the re-apply fails with "already exists in
   working directory" (34 files for `openvm-sha384`).
2. The verifier diffs `git diff HEAD`, so `git add -N .` is required after
   applying; otherwise every new file is invisible and the tree "differs".

## Result

| tree | `setup_*` | builds (`cargo test --lib --no-run`) |
|---|---|---|
| `pq-recursion` | OK (`setup_recursion_deps.sh`) | yes, 1m21s |
| `pq-stream-g2` | OK (`setup_cpu_fast_deps.sh`) | yes, 1m33s |
| `pq-cpu2` | OK (`setup_cpu_fast_deps.sh`) | yes, 1m26s |

`pq-stream-g2/bin/nv-g2s` rebuilt from the refreshed tree (11,426,336 B) via the
selection logic in `g2-gate/reproduce.sh`. Build outputs and `ckpt/`/`logs/`/`bin/`
were backed up first to `nearproof-deps/.tree-backups-20261021` (794 MB) and are
left in place.

## The refresh exposed a pre-existing stale test

`sha384::e2e_tests::{e2e_fib_child_debug, e2e_interactions_child_debug,
e2e_mutations_rejected}` now fail with

```
transcript replay disagrees with recorded sample at tidx 54
    (crates/recursion/src/transcript/sha_transcript.rs:241)
```

This is **not** caused by the refresh and **not** a soundness bug. It is a test
that no longer matches the protocol:

* `sha_transcript::replay_transcript` squeezes with
  `hash_parts(TAG_SQUEEZE, &[&state[..]])` — the **chained** transcript
  (σ_{j+1} = H(5, σ_j)).
* T\* (commit `46b7e62e2`, final-soundness G-1/G-2) replaced that with
  counter mode `B_j = H(5, κ ‖ le32(j))`, and its `git show` touches
  `replay_transcript` **zero** times. A parallel T\* implementation
  (`sha_transcript::replay2`, guarded by
  `assert!(sha_levers().tstar)`) is what the NV builder actually consumes.
* So `replay_transcript` is the legacy path, kept for `sha384::e2e_tests` debug
  helpers; the tests were never updated for T\*.

Why it only appeared now: no gate or script runs `sha384::e2e_tests`
(`grep -rn "sha384::e2e_tests" research/ docs/ --include=*.sh --include=*.md`
returns nothing), and before this refresh the trees did not match the pinned
patch, so "everything builds" was the only signal anyone had.

### What passes

`nv::` is the path that matters and it is green:

* both NV batch runs (`--skip nv_chain`, and a second excluding the three
  multi-proof tests) completed **55 tests with 0 failures**; they were stopped by
  the wall clock, not by a failure.
* `nv_tstar_tamper`, `nv_statement_digest`, `nv_lever_tamper`,
  `nv_whir_lever_tamper`, `nv_sample_word_source_tamper`,
  `nv_program_pow_identity`, `o2_agreement_table`, `o2_round0_multi_commit`,
  `nv_prep_cached`, `nv_tight_heights`, `nv_merkle_op_tamper` all pass.

### Follow-up (not done here)

Fix `sha384::e2e_tests` to use `replay2`/T\*, or mark the three tests `#[ignore]`
with a comment naming T\*. Leaving them red is the worst option: the next person
will read a red e2e test as a soundness regression. Preferred fix is to port the
debug helpers to `replay2`, since `replay_transcript` otherwise remains a
second, divergent transcript implementation in the tree.
