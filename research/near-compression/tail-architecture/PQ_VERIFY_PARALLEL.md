# Parallel PQ verify kernels — 2026-10-26

Implemented the first parallel verify kernels for the NPMULT03 PQ path and
measured: **serial 1.483 s -> 0.905 s** (8 C threads + 8 Rust threads, 16
logical CPUs), with the full correctness battery passing. Instrumentation,
kernel and measurements committed; no security parameter touched.

## What was implemented

`np_vmul.h` — a pthread-worker kernel for the two dominant poly kernels in
the C verify's lift chain, following the established `np_pairs`/`np_jl`
discipline (caller holds the existing whole lock; 16-polx block splits;
per-element independence so splits are order-safe; `polyvec_poly_pointwise`
is pure — the lazy `sprod_chunk` cache is NOT on this path). Wired into
`reduce_lift_aggregate_zqcnst` (both `polxvec_polx_mul` arms), gated at
`npe>=1024`, controlled by `LABRADOR_VMUL_THREADS` (falls back to
`LABRADOR_JL_THREADS`). The JL collapse parallelism already existed in the
verify path via `collaps_jlproj_raw` — this run simply enabled it.

**Bug found by the C verifier itself**: the first kernel version passed the
vector operand unoffset (`x` instead of `x+start`); the final `verify()`
rejected with "Linear garbage polynomials wrong". Proven fixed via (a) a
standalone parity harness (serial vs 4-worker byte-identical over 296,577
elements, both kernel variants) and (b) gate bisection — the packet
verifies at every threshold.

## Measurements (single observations, not p95; CPU8 serial, 8-11/8-15+24-31 parallel)

| Config | Total | wiring | opening | C round-0 lifts |
|---|---:|---:|---:|---:|
| serial (RAYON=1, CPU8) | 1,483 ms | 517 | 962 | 358 |
| VMUL=4, JL=4 | 1,306 ms | 521 | 788 | 226 |
| **VMUL=8, JL=8, RAYON=8** | **905 ms** | **132** | **770** | — |

RAYON=8 parallelizes the Rust constraint-wiring replay (data-parallel
across constraints — the same shape the prover's bitand phase already
exploits).

## Validation

- Standalone kernel parity: byte-identical outputs.
- Fresh prove WITH the parallel kernels: ready 3.181 s, packet 250,126 B,
  all 112 table/root mutations reject, 21 public mutations reject.
- Cross-verify: the parallel-proven packet fresh-verifies (1.293 s at 4t)
  with all four codec negative checks.
- Kernel-disabled baseline still passes (1.478 s).
- No rank/norm/parameter/transcript change anywhere.

## Path to <200 ms (not yet there)

0.905 s remains. The next levers, in measured order:
1. `aggregate_sparsecnst` (~225 ms round 0, still serial): the
   deferral/coverage-sorted accumulator needs a destination-run-parallel
   design preserving per-destination accumulation order (the exact
   pairs-kernel lesson). Designed, NOT implemented.
2. Rust statement rebuild (~200 ms serial): layout/bound/phi/statement
   rows are parallelizable; the Rust side must switch from
   `RAYON_NUM_THREADS` for wiring to dedicated pools.
3. C project (~44 ms) + amortize (~24 ms) + later-round residue.
4. Folding: once per-chunk verify is fast, per-BLOCK aggregate verify is
   the validator-relevant number.

Prove-side note: the same kernels serve proving (the prove path already
used parallel JL/pairs); the opening phase remains the 1–2 s prove blocker,
GPU unmeasured. Composed PQ security unproved throughout.
