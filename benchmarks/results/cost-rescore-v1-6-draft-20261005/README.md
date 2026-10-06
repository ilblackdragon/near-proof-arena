# Offline cost_v1 re-scoring: near-transfer-receipt-v1-6

**OFFLINE RE-SCORING under a DRAFT price model; not signed, not published, not a board.** Price model `pm-near-mainnet-2026q4@v1` (draft), digest `sha256:38c281cfe256d2cfcdef920eb267254df16fbe947a76e03637ad704016b84dac`.

Prices: `validators_per_chunk=84`, `prover_vcpus=8`, `verifier_vcpus=8`, `cpu_fusd_per_vcpu_second=7610000000`, `bandwidth_fusd_per_byte=82000`, `storage_fusd_per_byte=0`, `prepare_amortization_requests=0`

Approximations: proof bytes per run = batch_size x proof_bytes_max (sessions predate per-run byte totals); same for baseline and candidates; verify per run = exact sum of the run's verify wall times (flat verify_runs_ns chunked by batch_size); verify was measured on the full 8-CPU benchmark set = verifier_vcpus of this model; prepare not charged (prepare_amortization_requests = 0).

## Scores

| candidate | submission | speed (live) | cost_v1 | cost CI ± | N_v=1 | N_v=30 | N_v=105 | bw=0 | bw=x1.8 (egress 0.09/GB) | verify on 2 vCPUs (price only) |
|---|---|---|---|---|---|---|---|---|---|---|
| reexec-npai | `sub_7ef24373…` | 97.324 | **207.592** | 0.599 | 199.488 | 207.383 | 207.615 | 1942.188 | 155.003 | 115.931 |
| reexec-witness | `sub_c67dd93b…` | 98.376 | **93.492** | 2.074 | 93.564 | 93.494 | 93.492 | 92.388 | 93.922 | 94.479 |
| reexec-witness-fast | `sub_314aa809…` | 110.007 | **91.318** | 1.001 | 91.807 | 91.330 | 91.317 | 88.970 | 92.203 | 93.337 |
| np-udr-stark | `sub_19cc9c90…` | 0.052 | **1.528** | 0.001 | 0.926 | 1.502 | 1.531 | 6.115 | 1.177 | 0.893 |
| np-udr-stark-fast | `sub_56bb976b…` | 0.048 | **1.496** | 0.002 | 0.949 | 1.475 | 1.498 | 6.098 | 1.151 | 0.874 |

## Per-class cost per batch of 8 requests (USD; validator terms include N_v)

| candidate | class | prove | N_v x verify | N_v x bandwidth | total | baseline total | verify ms/batch | proof KiB/batch |
|---|---|---|---|---|---|---|---|---|
| *reference (baseline)* | batch-1 | $0.000000 | $0.000192 | $0.000060 | $0.000253 | — | 37.6 | 8.5 |
| *reference (baseline)* | batch-16 | $0.000000 | $0.000654 | $0.000408 | $0.001062 | — | 127.8 | 57.9 |
| *reference (baseline)* | batch-256 | $0.000001 | $0.006981 | $0.004610 | $0.011592 | — | 1365.0 | 653.7 |
| np-udr-stark | batch-1 | $0.000121 | $0.017601 | $0.107753 | $0.125475 | $0.000253 | 3441.9 | 15276.9 |
| np-udr-stark | batch-16 | $0.000395 | $0.023322 | $0.135614 | $0.159331 | $0.001062 | 4560.6 | 19226.9 |
| np-udr-stark | batch-256 | $0.003784 | $0.031706 | $0.169589 | $0.205079 | $0.011592 | 6200.0 | 24043.9 |
| reexec-witness-fast | batch-1 | $0.000000 | $0.000194 | $0.000062 | $0.000257 | $0.000253 | 38.0 | 8.9 |
| reexec-witness-fast | batch-16 | $0.000000 | $0.000772 | $0.000459 | $0.001231 | $0.001062 | 150.9 | 65.1 |
| reexec-witness-fast | batch-256 | $0.000001 | $0.007951 | $0.004682 | $0.012633 | $0.011592 | 1554.7 | 663.8 |
| np-udr-stark-fast | batch-1 | $0.000186 | $0.017951 | $0.114608 | $0.132745 | $0.000253 | 3510.3 | 16248.8 |
| np-udr-stark-fast | batch-16 | $0.000556 | $0.023716 | $0.140363 | $0.164635 | $0.001062 | 4637.5 | 19900.3 |
| np-udr-stark-fast | batch-256 | $0.002963 | $0.031911 | $0.170210 | $0.205084 | $0.011592 | 6240.1 | 24131.9 |
| reexec-npai | batch-1 | $0.000000 | $0.000028 | $0.000081 | $0.000110 | $0.000253 | 5.5 | 11.5 |
| reexec-npai | batch-16 | $0.000000 | $0.000037 | $0.000603 | $0.000640 | $0.001062 | 7.2 | 85.5 |
| reexec-npai | batch-256 | $0.000001 | $0.000220 | $0.004864 | $0.005085 | $0.011592 | 43.0 | 689.6 |
| reexec-witness | batch-1 | $0.000000 | $0.000197 | $0.000063 | $0.000260 | $0.000253 | 38.6 | 8.9 |
| reexec-witness | batch-16 | $0.000000 | $0.000707 | $0.000499 | $0.001207 | $0.001062 | 138.3 | 70.8 |
| reexec-witness | batch-256 | $0.000001 | $0.007725 | $0.004410 | $0.012136 | $0.011592 | 1510.6 | 625.3 |
