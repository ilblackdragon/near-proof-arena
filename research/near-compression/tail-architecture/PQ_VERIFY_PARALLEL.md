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

## Update 2: aggregate short-macro kernel (later 2026-10-26)

Implemented `np_shortmac.h`, the destination-region parallel kernel for
`aggregate_sparsecnst`'s deferred short-macro accumulation (the 78 ms
round-0 block): each worker owns a PRIVATE int32 accumulator for a
contiguous destination region and processes every shortent CLIPPED to its
region in the caller's sorted order — per-element accumulation order is
exactly the serial one, and clipping cannot increase per-element coverage,
so the int32 headroom bound is unchanged. `shortent`/`shortmac`/
`shortent_cmp`/`DPWSSD` moved to chihuahua.h as shared static-inline.
Serial fallback intact; env `LABRADOR_SM_THREADS`.

Three real bugs found on the way (all caught before landing, each a
lesson): the job struct declared the phi pointer as `int32_t*` so C
pointer arithmetic stepped 4 bytes into polx arrays (caught by gdb
address math: `&phi[11096]` was only +41,824 B); the worker's stack
conversion buffer broke `_mm512_load_si512` alignment (worker stacks are
not 64B-aligned — heap-allocate worker buffers); and a local named `N`
collided with `data.h`'s `#define N 64`.

Parity: 150 synthetic entries with boundary-crossing/overlap/odd-wid/
gaps — serial vs 4-worker byte-identical. Phase effect: short_macro
78 -> 60 ms at SM=4. Full battery: verify passes with all codec
negatives; prove with kernels (250,126 B) cross-verifies; the forged
counterexample and trie mutants still reject under parallel kernels.

Honest measurement note: the box was under heavy external load during
final timing (load average 17.5, another lane's checker processes at
100% CPU); back-to-back runs under equal load show the parallel set ~13%
faster than serial, but ABSOLUTE numbers from that window are invalid —
the 0.905 s figure predates this kernel and the load, and re-measurement
on a quiet machine is required before quoting any new total.

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
