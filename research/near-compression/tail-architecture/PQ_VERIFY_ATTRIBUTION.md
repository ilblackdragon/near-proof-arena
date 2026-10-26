# PQ verify phase attribution — 2026-10-26

Full serial (RAYON=1, CPU8) attribution of the 1.47 s NPMULT03 fresh verify,
804-receipt packet, 250,126 B. One observation per configuration; not p95.
No security parameter, rank, norm or transcript change — instrumentation
only, reading clocks between existing phases.

## Top-level split (Rust VerifierTiming, printed by the verify path)

| Phase | ms | Share |
|---|---:|---:|
| wiring (frontend constraint replay) | 520–603 | ~36% |
| opening (Rust rebuild + C composite) | 947–1,073 | ~64% |
| reduce (IOP sumcheck) | 3.1 | 0.2% |
| commitment / switch / packet decode | ~0.4 | ~0% |

The IOP sumcheck is negligible; the "serial bottleneck" is NOT sumcheck
replay. Within the opening (Rust VerifyTimings + bridge marks):

| Opening sub-phase | ms |
|---|---:|
| rebuild (layout 13 + bound 10 + phi 11 + statement 116) | ~199 |
| labrador bridge: check_statement | 5.3 |
| labrador bridge: build_raw_statement | 0.2 |
| C composite_verify_simple | **~726** |

## C composite split (np_profile marks, LABRADOR_PROFILE=1)

| C sub-phase | ms | Notes |
|---|---:|---|
| simple_reduce (round 0, r=31, n=9567) | ~647 | the real cost |
| — lifts (LIFTS × jlproj/collaps/lift-aggregate) | 358 | 49% of all C time |
| — aggregate (simple + sparsecnst) | 221 | 30% |
| — project | 44 | |
| — amortize | 24 | |
| 5× reduce rounds (r=12,6,3,5,4) | ~80 | lifts ~58 dominant |
| final verify (r=4, n=299) | 0.1 | negligible |

## Implication for the <200 ms target

The three big costs — C lifts/aggregate (579 ms), Rust wiring (520 ms),
statement build (117 ms) — are all bulk poly-matrix/vector loops over
independent elements:

1. C lifts + aggregate: the same op families the prover already
   parallelizes via np_pairs/np_jl pthread workers (polxvec_sprod_add /
   collaps chains), under the existing whole-operation lock. A 4-worker
   port of the two verify kernels (retaining per-output accumulation
   order and the sprod chunk-cache warmup discipline from the proving
   patches) bounds the 579 ms at ideal ~145 ms.
2. Rust wiring: sumcheck-replay of per-constraint evaluations —
   data-parallel across constraints; the prover's bitand phase already
   parallelizes the same shapes (729 ms -> 217 ms with 4 threads there).
3. Statement build (116 ms): matrix construction, parallelizable rows.

Ideal 4-way stacking (serial fraction ~35 ms: bridge+rebuild+reduce+decode)
bounds serial verify near 35 + (579+520+117)/4 ≈ 35 + 304 ≈ 340 ms.
16-way bounds it near 35 + 64 ≈ 100 ms — under the 200 ms target, but
measured on only 4 physical cores pinned here; the 16-thread numbers must
be measured, not extrapolated. The wiring phase may also shrink with the
Rust rayon pool (the parallel-verify observation of 1.44x at 4 threads was
measured before this attribution and included unparallelized C).

## Reproduction

Instrumented (this commit): labrador.c reduce()/verify() marks,
dachshund.c simple_reduce marks (np_profile.h), Rust
VerifierTiming/OPENING_PHASES prints in the driver verify path, and
LABRADOR_BRIDGE marks in labrador::verify. Verify with:

```
LABRADOR_PROFILE=1 RAYON_NUM_THREADS=1 \
NEAR_LEDGER=... NEAR_TRIE=... NEAR_VERIFY_EXPORT=PACKET \
NEAR_EXPECTED_PUBLIC=PUBLIC taskset -c 8 near-receipt-multi 16,16,1024 compact
```

Fixtures: the committed NPMULT03 packet (250,126 B) verifies fresh; all
four codec negative checks pass in the same run. Backward snapshot:
labrador-before-verify-profile.c in the backend directory.

## Open

Parallel verify kernels are NOT implemented — this is attribution only.
The 200 ms goal additionally needs folding (per-block aggregate verify)
for the validator-economics case, and composed PQ security is unproved.
The 1–2 s prove side needs the same C-kernel parallelism plus the opening
phase; GPU remains unmeasured.
