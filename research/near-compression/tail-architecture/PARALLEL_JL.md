# Parallel JL matrix collapse

2026-10-24. Original 804-receipt source/outcome list: **244,814 B**, with warm
packet readiness **3.004 / 3.108 s** on four physical CPU cores. The same build
with serial JL collapse takes **3.095 / 3.281 s**. This is a small measured
improvement, not a two-second guarantee or full NEAR proof.

## Implementation and checks

`np_jl.h` wraps the unchanged `polxvec_jlproj_collapsmat`. Workers receive
contiguous output slices whose starting offsets are multiples of 16 polynomials.
Matrix offsets advance by exactly `256*N/8` bytes per polynomial. Only the last
worker receives the original partial final block. Thus each block uses the same
challenge, arithmetic and representation as the original function. Each worker
owns local scratch and disjoint output; the challenge and matrix are read-only.
Workers join before projection collapse and subsequent transcript operations.

`LABRADOR_JL_THREADS` defaults to 1, accepts 1–16, and falls back to 1 for invalid
values. The proof path stays serial below 1024 polynomials. Failed thread
creation runs the corresponding disjoint job on the caller. Failed join aborts.
The whole-prover lock remains necessary; this does not authorize concurrent C
proofs. Security parameters, commitments and transcript sequencing are unchanged.
The original routine and its scalar/non-matrix companion are retained.

The harness compares every raw output byte against the unchanged serial routine:
306 cases spanning lengths 0/1/15/16/17/31/32/33/47/48/49/127/128/129/1023/1024/1025,
workers 1/2/3/4/8/16, and zero/all-one/pseudorandom matrices. Three additional
comparisons use 296,577 polynomials (31*9567). Boundary cases exercise unequal
partitions and partial final blocks. Isolated large timings: serial 91–132 ms,
four workers 31–41 ms. These timings are not the integrated lifting timings.

## Integrated measurements

Ryzen 9 9950X3D, cores 8–11; native release build; 16 GiB virtual-memory limit.
Both modes keep Rayon, Rust commitment and pair-product workers at four. Only
JL worker count changes. Profiling is enabled. Each process builds circuit/setup
once and proves the original fixture twice; warm readiness excludes that setup.

| JL workers | Three initial JL lifts combined, ms | Warm readiness, s |
|---|---|---|
| 1 | 150.6 / 151.6 | 3.281 / 3.095 |
| 4 | 48.4 / 56.6 | 3.108 / 3.004 |

Seven public mutations reject per proof. The exported final parallel packet has
independently reconstructed expected public bytes. Fresh verification uses the
unchanged old serial-backend binary, pinned by hash; its log and result are in
the evidence manifest. It accepts in 1.499 s without receipt witnesses, with
backend roundtrip and four negative checks passing. Two samples per mode on a shared host do not establish
p95, and whole-proof timings overlap. The roughly 100 ms kernel reduction is
better supported than an exact end-to-end speedup factor. No GPU was used.

## Limits and next work

Lifting aggregation remains another substantial backend cost. Any parallelization
must review disjoint writes and shared initialization, preserve arithmetic order,
and pass exact parity plus the older verifier. More fundamentally, this proof
still lacks source inclusion in the chunk claim, authenticated state/context,
other incoming lists, general runtime/Wasm, complete outcome-root integration,
bounded history and composed PQ security. Component speed does not discharge
those obligations. The full 1–2 second goal remains unachieved.

## Reproduction

Apply `evidence/parallel-jl/parallel-jl.patch` after the parallel-pairs checkpoint.
It adds the header and its Makefile dependency. Build the stages binary with the
existing native RUSTFLAGS/backend path. Copy the archived test to the backend:

```
cc -std=c2x -O3 -march=native -fwrapv -DLOGQ=48 -pthread \
  test_np_jl.c liblabrador.a -lm -o test_np_jl
taskset -c 8-11 ./test_np_jl
LABRADOR_PROFILE=1 LABRADOR_JL_THREADS=4 LABRADOR_PAIR_THREADS=4 \
LABINIUS_COMMIT_THREADS=4 RAYON_NUM_THREADS=4 NEAR_EXPORT_DIR=EXPORT_DIR \
  taskset -c 8-11 near-receipt-list-stages 1024 compact ORIGINAL_LIST ORIGINAL_LIST
```

Use `LABRADOR_JL_THREADS=1` for the same-build control. Evidence retains the
header, narrow patch, test source, build/parity/proof/verification logs and
binary/source/packet hashes. Decoder use remains trusted-local; neither hostile
parser safety nor zero knowledge is established.
