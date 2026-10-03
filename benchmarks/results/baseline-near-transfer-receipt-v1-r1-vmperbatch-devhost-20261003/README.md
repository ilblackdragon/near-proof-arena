# vm_per_batch sessions (bench-spec-v1.1), reference candidate — DEV HOST, NOT PINNED

Three sessions of `examples/reexec-witness` with
`measurement.invocation_mode = vm_per_batch` (one Firecracker microVM per
measured batch, fresh process + wiped scratch per request, one untimed
warm-up invocation). The inputs were sampled under
`chl_f7eb2d91bf7b363eee134b6ad9d3e011` (v1.1). Images were built from this
checkout into a private deps dir. All gates PASS and every proof was
claim-checked and verified.

**All three sessions are infra-invalid under BENCHMARK_SPEC §6.1**: the
stand-in calibration drift/noise checks failed on the shared host (load
average 9.5–15.9). **No successor challenge was pinned from them.**

| attempt | start (UTC) | batch-1 / batch-16 / batch-256 median per 8-request batch (ns) | cold (per-invocation VM) | session drift ppm | pre / post noise ppm |
|-|-|-|-|-|-|
| 1 | 07:00 | 7 785 612 / 7 949 924 / 10 394 852 | 220 / 217 / 222 ms | 98 881 | 58 432 / 33 542 |
| 2 | 07:03 | 10 946 554 / 10 093 298 / 18 114 245 | 202 / 217 / 229 ms | 494 006 | 74 831 / 68 561 |
| 3 | 07:06 | 9 764 517 / 9 353 375 / 13 207 179 | 211 / 233 / 193 ms | 47 589 | 22 648 / 41 751 |

The direction of the effect is consistent across attempts. A steady-state
batch takes 8–18 ms, against ~205–216 ms per batch under vm_per_invocation
(`../baseline-near-transfer-receipt-v1-r1-devhost-20261003`), and cold
starts stay ~200 ms. The absolute values are not stable enough to pin.

Open item: re-run on a quiet or governed host, then pin
`near-transfer-receipt-v1-2` (= v1.1 + `invocation_mode: vm_per_batch` +
new `baseline_ns`) with `benchmarks/baseline/pin_baseline.py` and
`arena-admin supersede`.
