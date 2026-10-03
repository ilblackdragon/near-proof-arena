# Baseline session: near-transfer-receipt-v1, suite r1 — DEV HOST

**Not an official number.** Measured on the shared development host
(`dev-illia-32c`, AMD Ryzen 9 9950X3D; host warnings: `powersave` governor,
boost on, SMT on, no `isolcpus`), not on a governed host of the challenge's
hardware profile `nearproof-local-ryzen9-9950x3d`. Load average 14.6 at the
start, 3.4 at the end (other tenants). Produced by
`benchmarks/baseline/run_baseline.py` (see `benchmarks/baseline/README.md`).

| | |
|-|-|
| challenge measured | `chl_5ef2bc7d2068219635426e47ca46bfbb` (v1, `baseline_submission = null`) |
| reference package | `examples/reexec-witness`, git tree `6dfbc3bc…`, package digest `sha256:329c763a92542052e1e2d69b6dc262446571acb1ab9ec50fd4caec170bcd699f` |
| entry points | prepare `fffa46d5…`, prove `df7c1a0c…`, verify `3931ac6f…` (= the judge's native-lean build) |
| sandbox | Firecracker (production backend, no tier cap), cpus 8–15, one microVM per invocation |
| procedure | challenge `measurement`: cold 1, warm-up 3, measured 15, fresh-confirm 1, batch 8, median, MAD k = 5 |
| sampling | fresh secret, **revealed** in `summary.json` with its commitment; seeds per §11.1 |
| session | 2026-10-03 06:24–06:38 UTC, 846 s |

| class (weight) | median ns (T_run, 8 proves) | MAD | min / max | cold | fresh | verify median (per proof) | max proof bytes |
|-|-|-|-|-|-|-|-|
| batch-1 (20 %) | **213 592 463** | 21 271 372 | 182 932 973 / 260 695 869 | 185 372 551 | 200 332 747 | 33.1 ms | 1 245 |
| batch-16 (30 %) | **205 044 335** | 15 680 580 | 180 225 955 / 264 915 795 | 188 279 751 | 221 809 091 | 42.5 ms | 8 638 |
| batch-256 (50 %) | **216 310 937** | 7 027 981 | 166 626 558 / 273 301 306 | 173 848 070 | 190 586 565 | 195.8 ms | 82 019 |

* Gates: `BENCHMARK` PASS (no flags; the session's own score is meaningless —
  it ran with `baseline_ns = 1`), `RESOURCE_LIMITS` PASS (prepare 6.5 ms,
  public dir 110 B), `PROVER_RELIABILITY` PASS: all 480 benchmark proofs were
  claim-checked against the oracle and accepted by the Lean `verify`.
* Outliers (flagged, kept): batch-256 runs 3 and 5 (13.3 % < 20 % limit).
  Caching tripwire: not suspected (batch-16 fresh +8.2 %, below k·MAD).
* Calibration stand-in (sha256 of 256 MiB zeros, same sandbox and cpus):
  pre median 419.5 ms, post 425.4 ms, session drift 14 096 ppm (< 20 000),
  noise 3 079 / 11 153 ppm — passes; no governed reference median exists.
* `peak_rss_bytes` in `session.json` is the VMM cgroup peak (guest memory),
  not the prover's RSS.
* Per-proof time (~25 ms) is dominated by process start inside a freshly
  booted microVM with a cold guest page cache; in-process `engine::prove` is
  3–200 µs (examples/reexec-witness-fast/README.md). The three classes are
  therefore nearly equal here.

These medians are pinned as `baseline_ns` of
`chl_f7eb2d91bf7b363eee134b6ad9d3e011` (`near-transfer-receipt-v1-1`).
