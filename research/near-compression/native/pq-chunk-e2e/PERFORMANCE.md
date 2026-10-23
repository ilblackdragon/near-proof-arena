# D0a proving optimization pass — 2026-10-21

**No tested runtime change earned promotion. Keep the existing eight-thread
configuration.** The retained changes are profiling/provenance improvements,
immutable tool snapshots, and a checkpoint replay harness. The optional patches
are preserved as rejected experiments, not recommended defaults.

## Measured baseline

Original executable, eight threads on CPUs `8-15,24-31` (eight physical cores):

| Stage | Profiled wall time |
|---|---:|
| Base proving | 77.869 s |
| Recursion and final compression | 3,065.683 s |
| **Total proving** | **3,143.552 s — 52m 24s** |
| Separate verification | **2.083 s** |

The packet is **299,967 bytes**, identical to the previous successful run. It
excludes the 3,711,888-byte pinned, run/shape-specific setup. This remains the D0a
research fixture; D3, zero-knowledge masking, and established security are not
provided by this pass.

Sampled peak chain RSS was approximately 13.3 GiB. CPU samples put the DFT
butterfly at 27.20%, memory copies at 20.53%, and two SHA-384 kernels at 21.42%
combined. Perf reported no lost samples. Two Lean jobs shared the affinity set
during the baseline, so this is a shared-host measurement.

## Whole-final-proof replays

All replays use the same trusted L5 checkpoint. The final-phase timer includes
key generation, trace generation, proving, and the prover's native verification.
The whole-command timer additionally includes checkpoint/public-input checks and
final artifact checks. These are final-stage measurements, not full chunk times.

| Configuration | Final phase | Whole command | Sampled peak RSS | Result |
|---|---:|---:|---:|---|
| Eight threads, original allocation/copy paths | 521.749 s | 526.115 s | 12.61 GiB | Control passed |
| Eight threads, buffer reuse + direct leaf rows | 524.521 s | 528.954 s | 12.78 GiB | No demonstrated improvement; rejected |
| Sixteen threads, same candidate | — | — | — | Contaminated by another job; stopped and excluded |

Both completed replays produced byte-identical packets **and setup**, passed the
original verifier with the original setup pin, and passed all packet-tampering
checks. The approximately 0.5% timing difference is not evidence of a useful win.
The planned second eight-thread control was not run after external contention
invalidated the sequence; no speedup is claimed from this pair.

The sixteen-thread trial's first large commitment took 266.6 s versus 223.1 s
with eight threads. Later, another recursion-test process began using exactly
the same CPU set and prover CPU utilization collapsed. The trial was stopped;
its partial profile and `INVALID.json` are retained. Its full latency must not
be used in comparisons.

## DFT padding follow-up

The measured commitment uses `2^20 x 102` DFTs. At SIMD width 16, each row has a
scalar tail. `perf-dft-pad.patch` tests padding internal work rows to a SIMD
width, capped at 25% extra columns; the scatter emits only original columns.
Commitment dimensions, domains, and proof parameters stay unchanged.

Matched kernel trials ran on CPUs `0-7,16-23`, with eight threads, because the
other half of the CPU was occupied. Each process warmed up twice and measured
16 transforms of the same shape and deterministic input. These timings must
not be compared directly with the earlier CPU set.

| Internal padding | Median, trial A | Median, trial B |
|---|---:|---:|
| Off | 79.967 ms | 76.508 ms |
| On | 83.029 ms | 82.483 ms |

Outputs and checksums matched. Padding was slower in both trials, so it was
rejected before spending another full proving run on it. No full proof with
padding enabled is claimed.

## Correctness and retained tooling

- 720 borrowed-row versus unchanged flat leaf-hash cases passed: scalar/SIMD,
  both leaf framings, both layer hashers, empty/partial batches, and padded,
  interleaved, narrow/wide rows.
- Eight streamed versus in-memory proof configurations passed byte equality and
  verification (16 small diagnostic proofs, not production security parameters).
- Sixteen DFT shape/reuse cases passed against Plonky3's independent radix-2
  implementation **for each padding setting**, including `2^20 x 102`.
- Full baseline and completed proof replays passed independent verification,
  statement/program tampering, and four packet rejection controls.
- The rebuilt default (non-experimental) backend also passed final verification
  and all four packet rejection controls after the tooling changes.

`run.sh` and `replay_final.sh` now snapshot executables into the output directory.
This addresses a real failure: the external `target-classical` directory
vanished before baseline verification. The attempt failed to launch
`statepublic` (exit 101, not a proof rejection). Its log and metadata remain in
`verify-helper-missing.log` and `failed-profiles/`. The profiler's saved helper
matched the original `RUN.json` hash exactly; restoring it allowed verification
and rejection tests to pass. The table uses the successful verification attempt.

Profiles now include selected environment settings and host load, and release
builds retain line-table debug information. `summarize_profiles.py RUN...` writes
`TIMINGS.json`, including failed attempts. RSS is explicitly sampled; stage sums
exclude profiler report-generation/orchestration overhead.

## Reproducing experiments

`setup_perf.sh` validates the underlying pinned patches and applies the optional
experiment overlays in an isolated dependency tree. Use the normal `setup.sh`
and `build.sh` for the unchanged backend. The experiment tree defaults to the
buffer/copy candidates; **it is not a recommended faster backend**.

`replay_final.sh SOURCE OUT [LEVEL]` needs a trusted complete local run, including
its profiler snapshots; the default fixture and level are D0a/L5. Optional
`PROVER_BINARY` selects a saved executable. `NEARPROOF_DFT_REUSE=0` and
`NEARPROOF_LEAF_DIRECT=0` restore the original paths; `NEARPROOF_DFT_PAD=1` enables
the rejected padding experiment. None changes a security/protocol parameter.

The optional `perf-hash-check` and `perf-dft-check` binaries require
`--features perf-experiments` and the experiment dependency tree. The latter's
`bench` argument selects the measured-shape microbenchmark. Run through
`profile.py` and set affinity/thread count explicitly.

Raw profiles, counters, binary snapshots, and complete proofs are under
`/data/illia/nearproof-deps/pq-chunk-e2e/runs/opt-baseline-8` and
`/data/illia/nearproof-deps/pq-chunk-perf/`. Compact evidence is in
`../../results/pq-chunk-perf/`. Further optimization should wait for the real D3
workload rather than expanding this pass into a prover redesign.
