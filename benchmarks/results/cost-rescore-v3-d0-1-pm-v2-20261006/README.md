# Offline cost_v1 re-scoring: near-chunk-validation-d0-1

**OFFLINE RE-SCORING under the GOVERNED price model pm-near-mainnet-2026q4@v2; no run is modified; not a board.** Price model `pm-near-mainnet-2026q4@v2` (governed), digest `sha256:292f094206162f78ee3ad982a8082c11b49fc379ad04956275693d9ef4d5ca6a`.

Prices: `validators_per_chunk=50`, `prover_vcpus=8`, `verifier_vcpus=8`, `cpu_fusd_per_vcpu_second=7610000000`, `bandwidth_fusd_per_byte=82000`, `storage_fusd_per_byte=0`, `prepare_amortization_requests=0`

Approximations: reference prove = frozen baseline_ns; reference verify / bytes = the re-measured cost baseline session (2026-10-06T07:55:35+00:00, CPUs 0,1,2,3,4,5,6,7); verify per run = exact sum of the run's verify wall times; proof bytes per run = exact per-run totals (baseline and every candidate have them); verify was measured on the full 8-CPU benchmark set = verifier_vcpus of this model (8); prepare not charged (prepare_amortization_requests = 0).

## Controls

* verify drift control `session-control-1.json` vs the pinned session: **not counted: session infra-invalid (SESSION_DRIFT)** (tolerance 30000 ppm; d0-missing 41730 ppm, d0-quiet 11222 ppm, d0-transfers 18527 ppm)
* verify drift control `session-control-2.json` vs the pinned session: **PASS** (tolerance 30000 ppm; d0-missing 4041 ppm, d0-quiet 5342 ppm, d0-transfers 19673 ppm)
* verify vs the frozen speed-baseline session (other day; informational — not a paired control unless it sampled the same challenge id): outside tolerance (d0-missing 632.1 vs 913.3 ms, 307907 ppm, d0-quiet 813.6 vs 800.4 ms, 16461 ppm, d0-transfers 923.8 vs 853.9 ms, 81878 ppm)
* re-measured prove median vs frozen `baseline_ns` (§6.2, informational; the frozen value is used): d0-missing 12977 ppm, d0-quiet 33095 ppm, d0-transfers 26882 ppm

## Scores

| candidate | submission | speed (live) | cost_v1 | cost CI ± | ref as in session-control-2.json | N_v=1 | N_v=84 (v1 draft) | N_v=105 | bw=0 | bw=x1.8 (egress 0.09/GB) | verify on 2 vCPUs (price only) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| reexec-v3-d0-fast | `sub_2b51fbde…` | 104.566 | **78.766** | 1.535 | 79.513 | 78.931 | 78.764 | 78.764 | 77.734 | 79.533 | 81.422 |
| reexec-v3-d0 | `sub_0826bb9b…` | 4.504 | **74.600** | 3.662 | 75.308 | 66.229 | 74.679 | 74.702 | 73.515 | 75.410 | 76.855 |

## Per-class cost per batch (USD; validator terms include N_v)

| candidate | class | prove | N_v x verify | N_v x bandwidth | total | baseline total | verify ms/batch | proof KiB/batch |
|---|---|---|---|---|---|---|---|---|
| *reference (baseline)* | d0-missing | $0.000000 | $0.001924 | $0.000139 | $0.002064 | — | 632.1 | 33.1 |
| *reference (baseline)* | d0-quiet | $0.000000 | $0.002477 | $0.000066 | $0.002543 | — | 813.6 | 15.7 |
| *reference (baseline)* | d0-transfers | $0.000000 | $0.002812 | $0.000116 | $0.002929 | — | 923.8 | 27.7 |
| reexec-v3-d0 | d0-missing | $0.000012 | $0.003664 | $0.000140 | $0.003816 | $0.002064 | 1203.8 | 33.4 |
| reexec-v3-d0 | d0-quiet | $0.000008 | $0.002968 | $0.000070 | $0.003045 | $0.002543 | 975.0 | 16.7 |
| reexec-v3-d0 | d0-transfers | $0.000009 | $0.003271 | $0.000106 | $0.003386 | $0.002929 | 1074.5 | 25.3 |
| reexec-v3-d0-fast | d0-missing | $0.000000 | $0.003495 | $0.000149 | $0.003645 | $0.002064 | 1148.2 | 35.5 |
| reexec-v3-d0-fast | d0-quiet | $0.000000 | $0.002810 | $0.000072 | $0.002882 | $0.002543 | 923.2 | 17.1 |
| reexec-v3-d0-fast | d0-transfers | $0.000000 | $0.003093 | $0.000099 | $0.003192 | $0.002929 | 1016.1 | 23.5 |
