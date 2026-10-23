# Verify-time profile of the 299,967 B packet (measured 2026-10-23)

Binary: `research/near-compression/native/pq-chunk-e2e` rebuilt,
sha256 `718def333d7313fc81152f9a5471ae2f4d951f497d664b096b3fb32656a4e4a6`.
Packet: `runs/opt-baseline-8/FINAL.bundle`, 299,967 B, sha256 `a1a2cce8…5bb248`.
Command (the only supported independent-verify path):

    nearproof-chunk-e2e verify AIR claim.bin statepublic SETUP.json <setup_sha256> FINAL.bundle

## Measured wall time and peak RSS

| `RAYON_NUM_THREADS` | wall (s), 2 runs | peak RSS |
|---:|---|---:|
| 1 | 7.65, 7.72 | 365 MB |
| 8 | 1.80, 1.77 | 427 MB |
| default (32 cores) | 1.46, 1.49, 1.48; separately 1.58 s | 488–496 MB |

Notes on earlier figures, so they are not misread:

* The run's own `TIMINGS.json` records `verify.wall_s = 2.08` and
  `sampled_peak_rss_gib = 0.196`. That stage includes process start, public-input
  preparation and the setup pin, so it is **not** the verifier in isolation. The numbers
  above are the same binary invoked directly.
* 1.46 s is the fastest reliably observed wall time; 1.58 s was observed once on the
  rebuilt binary before this table. Treat the honest band as **1.46–1.58 s at 32 threads**.
* Peak RSS moves *up* with thread count (365 → 496 MB), which is expected for parallel
  per-round work but is worth knowing against a 512 MB budget.

## What the scaling says

* 1 → 8 threads: 7.69 s → 1.785 s, a **4.3× speedup** on 8 threads.
* 8 → 32 threads: 1.785 s → 1.48 s, only a further **1.2×** on 4× the cores.
* So the verifier is **latency-bound** past ~8 threads, not throughput-bound. The
  practical statement is: **≈1.5 s on a normal multi-core machine, ≈7.7 s pinned to one
  core**, and adding cores past 8 buys little.

## What is NOT measured here

* No profile of *where* the 1.5 s goes (setup pin, WHIR query verification, GKR,
  relations, stacking). The section split of the *proof* is known, but not the time split
  of verification, so no claim is made about which section dominates.
* No verify-time measurement for any aggregation node. The depth-2/3/4 runs recorded prove
  time only.
* The 1 Pgas target implies a taller stack and a larger vk; verify time there is unmeasured
  and would not be expected to stay at 1.5 s.

## Why this matters for the objective

The objective treats prove **and** verify time as first-class. Verify is currently ~1.5 s
against a multi-hundred-second prove, so it is not the bottleneck: prove is ~340× verify
for the final layer alone (522 s vs 1.5 s) and the whole chain is ~3,144 s. Any work that
trades prove time for verify time would be moving in the wrong direction by two orders of
magnitude.
