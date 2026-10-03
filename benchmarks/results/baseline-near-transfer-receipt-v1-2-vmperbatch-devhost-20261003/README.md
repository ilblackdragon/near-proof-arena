# Baseline session: near-transfer-receipt-v1-2 (vm_per_batch), suite r1 — DEV HOST

**Not an official number.** This session ran on the shared development host
(AMD Ryzen 9 9950X3D, `powersave` governor, boost on, SMT on, no `isolcpus`).
That is not a governed host of the challenge's hardware profile. The
session was pinned to the four quietest physical cores, both SMT threads
each (CPUs 4–7 and 20–23). Load average was 10.2 at the start and 12.2 at
the end.

| | |
|-|-|
| measured challenge | unsigned pre-baseline draft `chl_30f39d9bf301f7ca2a8626850576ffc6` (`challenges/drafts/near-transfer-receipt-v1-2.measure.json`) = v1.1 + production checker pin + `invocation_mode: vm_per_batch`, baseline null |
| pinned in | `chl_3be93793610370275ae40f36a475f01f` (`near-transfer-receipt-v1-2`) |
| reference package | `examples/reexec-witness`, `sha256:329c763a92542052e1e2d69b6dc262446571acb1ab9ec50fd4caec170bcd699f`; verifier = judge native-lean build `sha256:3931ac6f…` |
| how | `benchmarks/baseline/run_baseline.py` → `runners/worker/examples/bench_session.rs`: the integrated worker's BENCHMARK stage, an `ExecJob` on Firecracker (rootfs `sha256:bb60e932…`, steps mode, deps `/data/illia/nearproof-deps/firecracker-rc`); batches sampled by the worker's NEAR oracle (public seeds over the measured challenge id and package digest) |
| procedure | cold 1 (one VM per invocation), warm-up 3, measured 15, fresh-confirm 1; batch 8 + 1 untimed warm-up invocation per batch VM |
| session | 2026-10-03 07:52–07:54 UTC |

| class | median ns (8 proves) | MAD | min / max | cold | fresh | verify median | max proof B |
|-|-|-|-|-|-|-|-|
| batch-1 | **6 828 348** | 303 840 | 6 308 816 / 20 697 847 | 226 713 660 | 7 465 885 | 5.0 ms | 1 319 |
| batch-16 | **7 226 875** | 571 483 | 6 238 605 / 9 147 612 | 222 626 003 | 7 279 974 | 18.2 ms | 7 456 |
| batch-256 | **10 195 296** | 758 477 | 8 344 109 / 13 014 643 | 272 318 781 | 9 534 301 | 182.9 ms | 81 156 |

* `BENCHMARK` PASS. Every proof, including the warm-up invocations, was
  claim-checked against the oracle and accepted by the judge verifier. The
  measured challenge has no baseline, so the session was measured, not
  scored.
* Outliers were flagged and kept: batch-1 runs 6 and 10 (13.3 %, under the
  20 % limit). The caching tripwire did not fire.
* Calibration (stand-in workload): drift 7 215 ppm, under the 20 000 ppm
  limit; noise 12 571 / 12 880 ppm, under the 20 000 ppm limit. **OK.**
* `invalid-attempt1/`: an earlier session on CPUs 0–7 failed calibration
  (drift 161 020 ppm, noise 146 197 ppm) and was not used. `retry.log`
  lists the spaced retries.
