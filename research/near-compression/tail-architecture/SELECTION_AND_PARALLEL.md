# Selection experiment rejected; four-core prover measured

2026-10-24. **244,814 bytes / 3.72–3.77 s on four CPU cores** for the original
804-receipt source/outcome relation. Fresh single-core verification passes.
The deadline and full NEAR/PQ/history requirements remain unmet.

## Bitmask selection result

The alternative computes `f XOR ((t XOR f) AND SAR(condition,63))`, preserving
MSB-boolean semantics without assuming other condition bits are zero. Shared
word-shift masks are computed once per stage. It replaces direct packed-concat
selections; upstream byte-shift helpers are unchanged.

Correctness checks pass: 625 short + 410 wide dirty-suffix cases, 46,062 rejected
mutations; the existing 2,170 source/outcome cases, 56,108 rejected mutations and
three in-memory proofs; exact source-byte limit acceptance, one-byte-over
rejection and acceptance under the larger profile.

It does **not** reduce the circuit representation:

| Same 16-slot compact relation | Existing | Bitmask variant |
|---|---:|---:|
| Private words | 112,734 | 114,931 |
| AND constraints | 55,594 | 78,752 |
| Zero constraints | 13,897 | 16,094 |
| Witness log | 16 | 16 |

The 1,024-slot masked build fails during construction under the 16 GiB virtual
cap (11,075,084 KiB peak RSS; failed 2 GiB allocation; 21.63 s). No large proof
exists for it. The baseline succeeds at that limit. Fewer binary-multiplication
operations do not imply fewer stored words; the replacement creates additional
intermediate constraints. **Keep the existing selector implementation.**
Rejected source and successful small checks are preserved separately.

## Existing implementation with four cores

No circuit/backend change: run the existing `near-receipt-list-budget` with
`RAYON_NUM_THREADS=4` and affinity CPUs8–11 (four distinct physical cores).
Pinned Binius includes Rayon loops; the previous CPU8-only measurements allowed
only one CPU. The lattice backend is not automatically parallelized by Rayon.

| Stage (ms) | First run | Second run |
|---|---:|---:|
| Witness packing | 41.2 | 41.6 |
| Commitment | 637.1 | 627.2 |
| Bitwise / binary-product reductions | 788.2 | 749.5 |
| Wiring / shift reductions | 259.3 | 286.8 |
| Field switch | 211.0 | 148.1 |
| Opening / compression | 1,768.1 | 1,798.3 |
| Total prover | 3,713.0 | 3,659.9 |
| Read/fill/prove/export | 3,770.0 | 3,716.1 |

Packets are **244,814 B**, including the fixed-capacity/mode selector. Expected
public bytes match independently generated original-list fixtures. All seven
public mutations per run reject. Fresh verification with `RAYON_NUM_THREADS=1`
and CPU8 takes **1.448 s**, needs no receipt witnesses, reproduces backend bytes,
and rejects selector/root/tape mutations. Four-core proving process peak RSS:
12,617,432 KiB. These two warm observations are not p95 and exclude cold setup
and original claim/witness preprocessing.

## Decision and next work

More Rayon threads alone cannot remove the measured ~2.4 s spent in commitment
and opening. Inspect those stages directly before another thread-count sweep.
`OpeningProof::timings()` already exposes fold, encoding, witness, T_R, masks,
phi, statement and LaBRADOR timings; record that breakdown on the next proof.
Any parallel backend work must preserve transcript ordering and avoid shared
C randomness/workspace races. No changes to security policy are justified by
this performance result.

The source-byte-limited profile is not a universal NEAR bound; the full-size
profile remains available. Source inclusion in the chunk claim, authenticated
state/context, other receipt lists, full runtime, composed PQ128 and bounded
history recursion remain required. Do not report this relation as full validity.

## Reproduction

```
RAYON_NUM_THREADS=4 NEAR_EXPORT_DIR=EXPORT_DIR taskset -c 8-11 \
  near-receipt-list-budget 1024 compact ORIGINAL_LIST
RAYON_NUM_THREADS=1 NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC \
  taskset -c 8 near-receipt-list-budget 1024 compact
```

Use the source-byte-budget checkpoint binary and 16 GiB virtual memory cap.
All logs, exact rejected source, hashes and affinity details are retained in
`evidence/selection-and-parallel`.
