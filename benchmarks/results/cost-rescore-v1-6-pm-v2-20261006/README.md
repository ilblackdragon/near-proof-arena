# Offline cost_v1 re-scoring: near-transfer-receipt-v1-6

**OFFLINE RE-SCORING under the GOVERNED price model pm-near-mainnet-2026q4@v2; no run is modified; not a board; reference verify UNCONFIRMED (VERIFY_DRIFT, BENCHMARK_SPEC 14.4): indicative only.** Price model `pm-near-mainnet-2026q4@v2` (governed), digest `sha256:292f094206162f78ee3ad982a8082c11b49fc379ad04956275693d9ef4d5ca6a`.

Prices: `validators_per_chunk=50`, `prover_vcpus=8`, `verifier_vcpus=8`, `cpu_fusd_per_vcpu_second=7610000000`, `bandwidth_fusd_per_byte=82000`, `storage_fusd_per_byte=0`, `prepare_amortization_requests=0`

Approximations: reference prove = frozen baseline_ns; reference verify / bytes = the re-measured cost baseline session (2026-10-06T08:06:51+00:00, CPUs 0,1,2,3,4,5,6,7); verify per run = exact sum of the run's verify wall times; proof bytes per run = batch_size x proof_bytes_max (some sessions predate per-run byte totals); same for baseline and candidates; verify was measured on the full 8-CPU benchmark set = verifier_vcpus of this model (8); prepare not charged (prepare_amortization_requests = 0).

## Controls

* verify drift control `session-control-1.json` vs the pinned session: **not counted: session infra-invalid (SESSION_DRIFT)** (tolerance 30000 ppm; batch-1 6403 ppm, batch-16 214389 ppm, batch-256 14585 ppm)
* verify drift control `session-control-2.json` vs the pinned session: **FAIL VERIFY_DRIFT** (tolerance 30000 ppm; batch-1 21948 ppm, batch-16 160774 ppm, batch-256 19546 ppm)
* verify vs the frozen speed-baseline session (other day; informational — not a paired control unless it sampled the same challenge id): outside tolerance (batch-1 38.9 vs 37.6 ms, 33644 ppm, batch-16 157.2 vs 127.8 ms, 229695 ppm, batch-256 1524.0 vs 1365.0 ms, 116492 ppm)
* re-measured prove median vs frozen `baseline_ns` (§6.2, informational; the frozen value is used): batch-1 98370 ppm, batch-16 135609 ppm, batch-256 20341 ppm

## Scores

| candidate | submission | speed (live) | cost_v1 | cost CI ± | ref as in session-control-2.json | N_v=1 | N_v=84 (v1 draft) | N_v=105 | bw=0 | bw=x1.8 (egress 0.09/GB) | verify on 2 vCPUs (price only) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| reexec-npai | `sub_7ef24373…` | 97.324 | **222.554** | 0.641 | 231.354 | 213.516 | 222.643 | 222.669 | 2187.299 | 162.731 | 118.352 |
| reexec-witness | `sub_c67dd93b…` | 98.376 | **100.270** | 2.225 | 104.235 | 100.144 | 100.271 | 100.271 | 104.549 | 98.623 | 96.469 |
| reexec-witness-fast | `sub_314aa809…` | 110.007 | **97.942** | 1.073 | 101.815 | 98.263 | 97.939 | 97.938 | 100.688 | 96.821 | 95.311 |
| np-udr-stark-fast2 | `sub_ec1fdc22…` | 0.070 | **1.632** | 0.003 | 1.696 | 1.087 | 1.640 | 1.642 | 6.725 | 1.233 | 0.909 |
| np-udr-stark | `sub_19cc9c90…` | 0.052 | **1.628** | 0.001 | 1.692 | 0.991 | 1.639 | 1.642 | 6.656 | 1.231 | 0.906 |
| np-udr-stark-fast | `sub_56bb976b…` | 0.048 | **1.596** | 0.002 | 1.659 | 1.016 | 1.604 | 1.607 | 6.672 | 1.205 | 0.887 |

## Per-class cost per batch (USD; validator terms include N_v)

| candidate | class | prove | N_v x verify | N_v x bandwidth | total | baseline total | verify ms/batch | proof KiB/batch |
|---|---|---|---|---|---|---|---|---|
| *reference (baseline)* | batch-1 | $0.000000 | $0.000118 | $0.000035 | $0.000153 | — | 38.9 | 8.3 |
| *reference (baseline)* | batch-16 | $0.000000 | $0.000479 | $0.000278 | $0.000757 | — | 157.2 | 66.1 |
| *reference (baseline)* | batch-256 | $0.000001 | $0.004639 | $0.002434 | $0.007073 | — | 1524.0 | 579.7 |
| reexec-witness | batch-1 | $0.000000 | $0.000117 | $0.000037 | $0.000155 | $0.000153 | 38.6 | 8.9 |
| reexec-witness | batch-16 | $0.000000 | $0.000421 | $0.000297 | $0.000719 | $0.000757 | 138.3 | 70.8 |
| reexec-witness | batch-256 | $0.000001 | $0.004598 | $0.002625 | $0.007224 | $0.007073 | 1510.6 | 625.3 |
| reexec-witness-fast | batch-1 | $0.000000 | $0.000116 | $0.000037 | $0.000153 | $0.000153 | 38.0 | 8.9 |
| reexec-witness-fast | batch-16 | $0.000000 | $0.000459 | $0.000273 | $0.000733 | $0.000757 | 150.9 | 65.1 |
| reexec-witness-fast | batch-256 | $0.000001 | $0.004733 | $0.002787 | $0.007520 | $0.007073 | 1554.7 | 663.8 |
| reexec-npai | batch-1 | $0.000000 | $0.000017 | $0.000048 | $0.000066 | $0.000153 | 5.5 | 11.5 |
| reexec-npai | batch-16 | $0.000000 | $0.000022 | $0.000359 | $0.000381 | $0.000757 | 7.2 | 85.5 |
| reexec-npai | batch-256 | $0.000001 | $0.000131 | $0.002895 | $0.003027 | $0.007073 | 43.0 | 689.6 |
| np-udr-stark | batch-1 | $0.000121 | $0.010477 | $0.064138 | $0.074737 | $0.000153 | 3441.9 | 15276.9 |
| np-udr-stark | batch-16 | $0.000395 | $0.013882 | $0.080722 | $0.095000 | $0.000757 | 4560.6 | 19226.9 |
| np-udr-stark | batch-256 | $0.003784 | $0.018873 | $0.100946 | $0.123603 | $0.007073 | 6200.0 | 24043.9 |
| np-udr-stark-fast | batch-1 | $0.000186 | $0.010685 | $0.068219 | $0.079090 | $0.000153 | 3510.3 | 16248.8 |
| np-udr-stark-fast | batch-16 | $0.000556 | $0.014117 | $0.083550 | $0.098222 | $0.000757 | 4637.5 | 19900.3 |
| np-udr-stark-fast | batch-256 | $0.002963 | $0.018995 | $0.101315 | $0.123273 | $0.007073 | 6240.1 | 24131.9 |
| np-udr-stark-fast2 | batch-1 | $0.000085 | $0.010685 | $0.063190 | $0.073959 | $0.000153 | 3510.0 | 15050.9 |
| np-udr-stark-fast2 | batch-16 | $0.000277 | $0.014345 | $0.082871 | $0.097493 | $0.000757 | 4712.6 | 19738.6 |
| np-udr-stark-fast2 | batch-256 | $0.002921 | $0.018816 | $0.099919 | $0.121656 | $0.007073 | 6181.2 | 23799.4 |
