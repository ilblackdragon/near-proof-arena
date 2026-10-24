# LaBRADOR backend phase attribution

2026-10-24. **Profiling only; no new speedup claim.** The existing best local
result remains 244,814 B / 3.13–3.30 s on four cores for one 804-receipt relation.
The 1–2 s deadline and full NEAR/PQ history requirements remain open.

## Where the backend time goes

The final instrumented run spends 1,456 ms in the C composite prover. Rust
statement/witness checks take 10.8 ms; constructing the raw statement and witness
adds 0.27/1.96 ms. Rank/security setup is below 1 ms across the C rounds.
Optimizing parameter search or the Rust/C boundary is therefore not the priority.

| Initial simple-statement phase | Milliseconds |
|---|---:|
| Commitment | 214.0 |
| Projection | 170.1 |
| Initial constraint evaluation | 33.1 |
| Constraint lifting, all three rounds | 453.5 |
| Apply deferred constraints | 92.1 |
| Aggregation | 128.3 |
| Amortization | 211.3 |
| Refresh | 13.8 |

The later recursive rounds total about 140 ms. Initial statement shape is
`r=31, n=9567`. Nested timings divide the 453.5 ms lifting phase into:

| Nested lifting operation | Milliseconds |
|---|---:|
| JL matrix collapse | 157.2 |
| Scalar collapse and intervening zero fill | 36.4 |
| Simple constraint collapse | 77.4 |
| Lift aggregation | 182.5 |

These nested entries must **not** be added again to the top-level total. Timings
cover the intervals between instrumentation points, including nearby allocation/
cleanup where applicable; they are not instruction-level profiles. C intervals
use `timespec_get(TIME_UTC)` and Rust intervals use `Instant`. This small set of
instrumented observations is not p95 or an isolated-host comparison.

## Next optimization candidate

The backend has distributed arithmetic costs, not a single cheap call to remove.
Inspect independent output pairs in `amortize`'s linear-garbage computation.
Partitioning output pairs while retaining each pair's original block/product
accumulation order could avoid shared writes and transcript reordering. Its cost
is currently included in the 211 ms amortization stage; no isolated pair-kernel
speedup has been measured yet. First measure that kernel and compare exact
serial/parallel outputs, then run the complete proof and old verifier.

Other candidates are disjoint coefficient updates in lifting and JL matrix
collapse. Do not parallelize entire proof rounds: later challenges depend on
earlier transcript messages. Do not reduce ranks/norm/security policy or share
mutable C random state among worker threads to obtain a latency number.

## Validation and evidence

The final packet remains **244,814 bytes**. Its public bytes match independent
original-list fixtures. In-process proof checks pass, and the unchanged older
serial-backend verifier accepts it freshly without receipt witnesses in 1.586 s;
selector/root/tape mutations reject and backend bytes roundtrip. The older binary
hash matches the source-byte-budget checkpoint. This supports protocol
compatibility of the instrumentation; it does not establish composed PQ128.

The first trace instrumented principle/recursive entry points, but this binding
uses `simple_prove`; it measured only the later recursive rounds. The complete
and detailed traces fix that coverage gap and are the attribution evidence.
The initial header-order build failure is retained; successful builds preserve
`_DEFAULT_SOURCE` before standard headers. Instrumentation leaves arithmetic,
transcript and parameter code unchanged.

The relation still lacks source inclusion, authenticated state/context, other
chunk lists, full runtime and bounded PQ history. Profiling does not close any
of those semantic/security obligations.

## Reproduction

Apply `evidence/labrador-phases/backend-profile.patch` to the isolated
stronger-policy C backend and `rust-profile.patch` to its LaBinius binding.
The Makefile records the new timing-header dependencies. Rebuild the existing
`near-receipt-list-stages` binary with the documented native flags and backend
path, then run with the established 16 GiB virtual-memory cap:

```
LABRADOR_PROFILE=1 LABINIUS_COMMIT_THREADS=4 RAYON_NUM_THREADS=4 \
NEAR_EXPORT_DIR=EXPORT_DIR taskset -c 8-11 \
  near-receipt-list-stages 1024 compact ORIGINAL_LIST
```

Detailed source snapshots, narrow patches, initial/complete/detailed logs,
aggregated timing JSON and source/binary/packet hashes are preserved in
`evidence/labrador-phases`. Output is opt-in through LABRADOR_PROFILE; timing
reads remain in the instrumented code when output is disabled.
