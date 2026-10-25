# Parallel amortization pair products

2026-10-24. The original 804-receipt source/outcome list still produces a
**244,814-byte** packet. Four pair workers give **3.15–3.34 s warm readiness**;
same-build serial pair runs give **3.51–3.56 s**, with all other thread settings
fixed. This supports a kernel improvement, not a two-second or full NEAR claim.
The earlier best 3.13 s observation is not surpassed by this small sample.

## Change and correctness

`np_pairs.h` partitions triangular output indices among up to 16 pthread workers.
Each worker retains the original outer block order (16 polynomials), and each
output retains the original order of the one or two scalar products per block.
Operands are shared read-only, outputs are disjoint, and workers join before
conversion, commitments or transcript challenges. The original whole-prover
lock remains necessary; this does not allow concurrent C proofs.

The caller initializes the lazy SPROD_WALK chunk cache serially before starting
workers. Thread creation failure runs that disjoint job on the caller; a join
failure aborts rather than freeing storage while workers may still be live.
`LABRADOR_PAIR_THREADS` defaults to 1, accepts 1–16, and falls back to 1 for
invalid settings. The proof path uses one worker when `r*n < 32768`. Tail
amortization and security/transcript parameters are unchanged. This pthread
implementation was tested on the existing Linux/glibc environment.

The standalone harness compares raw output bytes against the original serial
loop: 540 cases across r=1/2/3/6/12/31, n=1/15/16/17/33/127, zero/ternary/
almost-uniform inputs, and workers=1/2/3/4/8. It additionally checks first-use
cache initialization before any reference scalar product, and three exact
comparisons at r=31,n=9567. Initial large timings were 166–173 ms serial versus
58–86 ms with four workers. The initial harness build mistakenly used LOGQ=32
against the existing LOGQ=48 library and crashed; the corrected harness uses
48. The failed log is retained and is not part of the passing evidence.

## Full relation measurements

Both modes use four physical CPU cores (8–11 on Ryzen 9 9950X3D),
`RAYON_NUM_THREADS=4`, `LABINIUS_COMMIT_THREADS=4`, native release compilation,
and a 16 GiB virtual-memory cap. Profiling is enabled in both modes.

| Pair workers | Initial pair kernel, ms | Warm packet readiness, s |
|---|---|---|
| 1 | 152.8 / 156.0 | 3.558 / 3.515 |
| 4 | 44.5 / 57.2 | 3.344 / 3.147 |

Each process constructs the circuit/setup once and proves the same original
fixture twice. Seven public mutations reject per proof. Peak RSS is 12,869,656
KiB for the parallel process. Other host work was active; two observations per
mode are not p95 or a randomized benchmark. The paired timing difference cannot
all be attributed to this kernel: other stages also varied.

The exported final parallel packet's public bytes match independent reconstruction
from the original fixture. The unchanged older serial verifier is checked by
binary hash and accepts separately without receipt witnesses in 1.513 s;
backend re-encoding matches and all four negative checks reject. No GPU results are claimed.

## Remaining work

This saves roughly 100 ms in the dominant initial pair loop. Larger remaining
costs include constraint lifting, projection, commitment, and frontend work.
Next investigate disjoint output blocks in JL collapse and lifting, with exact
parity and cache/state review before whole-proof benchmarking.

The relation still covers one incoming receipt list with D0a transfer/outcome
logic. Source inclusion, authenticated state/context, other lists, general
runtime/Wasm, complete outcome roots and bounded recursive history are missing.
Composed PQ128 and zero knowledge are unestablished; the C decoder is for trusted
local exports. These changes do not relax security parameters or establish any
of those missing obligations.

## Reproduction

Apply `evidence/parallel-pairs/parallel-pairs.patch` after the amortization-profile
checkpoint. The new header is a Makefile dependency. Build the existing stages
binary with the documented native RUSTFLAGS/backend directory. For the standalone
harness, from the backend directory:

```
cc -std=c2x -O3 -march=native -fwrapv -DLOGQ=48 -pthread \
  test_np_pairs.c liblabrador.a -lm -o test_np_pairs
taskset -c 8-11 ./test_np_pairs
```

For the full original-list proof, use:

```
LABRADOR_PROFILE=1 LABRADOR_PAIR_THREADS=4 LABINIUS_COMMIT_THREADS=4 \
RAYON_NUM_THREADS=4 NEAR_EXPORT_DIR=EXPORT_DIR \
  taskset -c 8-11 near-receipt-list-stages 1024 compact ORIGINAL_LIST ORIGINAL_LIST
```

Set `LABRADOR_PAIR_THREADS=1` for the same-build serial control. Evidence includes
source snapshots, the narrow patch, standalone/build/proof/verification logs,
independent public audit and binary/packet hashes.
