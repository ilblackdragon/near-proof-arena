# Wasm vertical slice — measured ladder (Phase 3)

2026-10-28. The `near-wasm-exec` vertical slice (NPMWASM02 contract,
Phase 2, commits bfd11c9a2/730f4919e) measured on the KAT ladder with the
pinned protocol: CPU 8-11, 4 threads (RAYON_NUM_THREADS=4), 16 GiB
address-space cap, `/usr/bin/time -v`, two observations per rung.
**Load label: HIGH (box load avg ~52 on 32 cores during the runs)** —
wall-clock numbers are upward-noisy; treat them as load-labeled upper
bounds, not p95s (two observations only, per protocol).

## Ladder (addchain family; rung = circuit step capacity, fixture steps in parens)

| Rung | Suite (witness log) | AND | Private words | Prove s (obs1/obs2) | Verify s (obs1/obs2) | Packet B | RSS MB (obs1/obs2) |
|---|---|---|---|---|---|---|---|
| 8 (8) | sizes (17→fits 18) | 133,100 | 189,039 | 0.259 / 0.263 | 0.134 / 0.136 | 197,167 | 532 / 534 |
| 64 (64) | sizes (18, at boundary) | 211,685 | 330,703 | 0.330 / 0.326 | 0.180 / 0.173 | 201,679 | 717 / 719 |
| 512 (512) | sizem (20, at boundary) | 839,781 | 1,463,751 | 0.703 / 0.726 | 0.314 / 0.317 | 209,231 | 2,054 / 2,037 |
| 2048 (2044) | sizel (22, at boundary) | 2,993,253 | 5,348,487 | 2.026 / 2.012 | 0.661 / 0.650 | 157,367 | 6,288 / 6,258 |
| 2048 (memmix80, 2010) | sizel (22) | — | — | 1.933 / 1.918 | 0.648 / 0.647 | 158,647 | 6,272 / 6,264 |

Memory-heavy variant (memmix80: i64.store/load/load32_u/store32 churn
across 2010 steps) measures the same as the ALU-heavy rung — the
running-bank memory design (no read-over-write scan) keeps memory steps
at the ALU-step cost class.

## Per-step cost (the central datum)

- **~1,452 AND/step** at the 2048 bound (2,993,253 AND / 2048 slots of
  table capacity; the fixture used 2044). Sub-linear components (code
  digest, init digest: ~19 sha compressions ≈ 4,276 AND constants +
  per-word costs) amortize across steps.
- **vs the D0a transfer relation**: 4,792 AND/slot. The Wasm step slot
  costs **0.30x** — 3.3x cheaper per slot. (Both on the same frontend
  and backend; D0a slots are receipt-semantics, Wasm slots are one
  instruction each.)
- **vs the zkVM guest**: 10,387 rows/receipt on a non-PQ (Dory)
  pipeline at CPU-hours/chunk. Not directly comparable per row (a zkVM
  row is finer-grained than a Wasm instruction), but the Wasm slice
  proves a full instruction with its stack/locals/memory side-effects
  in-circuit at ~1.5k AND, on the PQ backend, at sub-second verify.

## Suite boundary (measured, not assumed)

Witness logs per rung: 17 / 18 / 20 / 22 — each rung lands exactly ON a
suite boundary (sizes=18, sizem=20, sizel=22). The suite snap means a
rung whose witness log is boundary+1 pays the NEXT suite's moduli set;
the 2048 rung at log 22 uses sizel. **The next rung (log 23-24) selects
sizexl (witness_log_len 24), whose moduli set swaps Q4861 for Q9721** —
a different moduli table than the corpus has measured. The 2048-step
cap comes from the known frontend dense-build wall (the scaling-ladder
work's [·,·,2048] wall); pushing past it needs the folded/recursive
composition, which is the Phase-4 integration question, not a silent
extrapolation.

## 1-Pgas chunk extrapolation (labeled: EXTRAPOLATION)

A 1-Pgas chunk ≈ 2-6 Gcycles of native Wasm (the goal's stated
planning band) ≈ 10^9-ish Wasm instructions at ~1-3 gas/insn (gas=1/op
is this slice's diagnostic profile, NOT the real NEAR table).

- At the measured ~1,452 AND/step: **~1.5-8.7 GAND-equivalents per
  1-Pgas chunk** (10^9 × 1.5k), vs the 2048-step rung's 3.0M AND.
  That is ~500-2,900x the current largest single-circuit rung —
  **compositional folding (per-block + recursive opening) is required,
  not a single monolithic circuit.**
- Packet bytes: the rungs measure 157-209 KB and are FLAT vs steps
  (the LaBRADOR commitment is dominated by the recursive opening, not
  the table size). The 300 KB packet target **survives folding**: even
  at the full ladder the single-rung packet stays ~0.16-0.21 MB, and
  folding adds per-fold overhead, not per-step bytes.
- Prove time scales ~linearly in steps (0.26s @ 8 → 2.03s @ 2048 ≈
  0.98 ms/step). At 1 Pgas: **~10^6 s of single-circuit CPU proving
  (impossible)** — confirming the verdict that the 1-2 s chunk-prove
  target needs GPU opening + folded per-block verify (the known
  levers), not this CPU path. The slice's job was semantic coverage at
  measured cost; that is achieved.

**What breaks first**: the frontend dense-build wall at the 2048-step
class (before gas/folding economics). The next scale rung must be the
folded composition, which is exactly the Phase-4 decision.

## Verdict

- Per-step circuit cost: **1,452 AND/step** — 3.3x under D0a's
  per-slot cost, on the same PQ backend. The slice is UNDER the
  relation's cost datum → **integrate (NPMULT04 composite) is the
  Phase-4 decision by measurement**, per the goal's decision rule.
- Verify: 0.13-0.66 s per rung on this box at high load — the <200 ms
  chunk-verify target holds only for the ≤64-step rungs; the 2048 rung
  needs the parallel-verify kernels (0.905s NPMULT03 baseline after
  VMUL=8/JL=8) and folding to reach the target.
- All numbers are two-observation, high-load; extrapolations labeled.
