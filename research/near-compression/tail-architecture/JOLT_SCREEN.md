# Current Jolt/Akita screen

2026-10-24; current source built and independently run on Ryzen 9 9950X3D.

## Measured results

CI profile, native CPU codegen, eight prover threads, affinity 8-15/24-31.
One sample per original workload; no GPU involved.

| SHA-chain scale | Requested 32-byte hashes | Prove | Actual proof bytes | Setup | Full process |
|---:|---:|---:|---:|---:|---:|
| 18 | 69 | 1.99 s | 97,998 | 0.112 s | 8.39 s |
| 20 | 277 | 7.46 s | 99,490 | 0.126 s | 7.87 s |

Both proofs verified in parallel and single-threaded modes. Scale 20 verification
was 12.907/28.960 ms respectively. The first process included first-run guest
preparation; it is not a warm latency comparison with the second.

A narrowly patched scale-18 rerun serializes, decodes with a byte limit, checks
complete consumption, and verifies the DECODED object. A midpoint-byte mutation
is rejected (decode error or verification failure). Result: 97,998 bytes,
1.96 s prove, 2.32 s full process, 10.586/19.584 ms verification. No independent
verifier process yet; public inputs and setup still come from the harness.

Evidence: `evidence/jolt/{manifest.json,original-timings.csv,wire-18.log,
wire-audit.patch}` and original scale logs. The proof blob remains in scratch,
pinned by SHA-256 in the manifest. None is a full NEAR or recursive-history proof.
The current CPU implementation misses the target already at this small workload;
proof byte size itself has substantial margin below 300 KB.

- Jolt `7931b223ddefe3cfa35671d0fa8321df4578ff96`.
- Pinned Akita `dfdbd7674cab5cfbe95243e947d1b10a982f232b`.
- Scratch `/data/illia/pq-tail-architecture-20261024/jolt`; original measurements
  use unchanged source, later wire-audit patch is preserved separately.

## What is implemented

The `akita` prover feature supplies lattice commitments, native batched openings,
sparse one-hot trace support and bincode serialization of the actual Jolt proof.
`crates/jolt-prover/src/profile.rs` measures setup separately, then times proving
after witness preparation. It measures the serialized proof length and verifies
the in-memory proof twice (parallel/single-threaded). It does NOT currently
establish independent deserialization or include tracing/witness construction
in its reported prover duration. The local patch adds roundtrip verification;
separate-process verification and application context binding remain open.

`examples/recursion` is not evidence of Akita history recursion: the SDK's
`VerifierPCS` aliases in `jolt-sdk/src/host_utils.rs` select Dory. Full NEAR
semantics, history composition and application binding still need implementation.

## Workload and revision comparability

`specs/akita-pr-1732-benchmarks.md` reports 1.42 s at 2^20 sha2-chain rows on
M4 Max, one sample per point, at August revisions. A different historical report,
`specs/akita-native-trace-batching-performance.md`, reports 89,173 B / 4.385 s.
Do not combine those into one measured latency/size pair.

At the current head, the harness targets 90% of the maximum rows, estimates
3,396 cycles/hash, and chooses floor(target/3396) iterations. Thus scale 20 asks
for 277 hashes. The guest hashes a 32-byte message each iteration: one SHA-256
compression per iteration. The sampled NEAR receipt workload requires 5,875
compressions, over 21 times as many, before other NEAR obligations. This is a
workload count comparison, NOT a timing extrapolation or reproduction of the
historical guest. Roughly scale 25 is needed for that many operations under the
current harness's calibration; actual trace counts must be measured.

Current Akita `book/src/how/security.md` describes `Quantum169BitADPS16` SIS
tables, whereas older reports used earlier policies. The document explicitly
limits this to a scalarized lattice attack-cost model and excludes several
structured attacks from that estimator. It separately describes 128-bit challenge
and Fiat-Shamir targets. These are not an application-level PQ128/QROM proof.
The Jolt outer Akita transcript is `LegacyBlake2bTranscript<AkitaField>` in
`crates/jolt-prover/src/akita/preprocessing.rs`; audit both transcript layers.

## Build attempts

The native release build reached final binary optimization but failed under
the 16 GiB virtual-memory bound: `rustc-LLVM ERROR: out of memory`. A final-crate
thin-LTO retry also failed. Disabling LTO only on the final crate cannot reuse
bitcode-only release dependencies: mold rejects objects without an LTO plugin.

Rebuilding all dependencies with upstream's `ci` profile (release optimization,
no LTO, no debug information) is the current path. Building the guest-build CLI
in the SAME Cargo invocation fails: the root SDK imports `jolt_prover::dory`,
which the Akita feature disables. Build them separately to avoid feature unification:

```sh
ulimit -v 16777216
RUSTFLAGS='-C target-cpu=native -C link-arg=-fuse-ld=mold' \
CARGO_TARGET_DIR=/data/illia/pq-tail-architecture-20261024/jolt-target \
taskset -c 8-15,24-31 cargo build --profile ci --locked -j 4 \
  -p jolt-prover --bin jolt-prover --features akita,profiling,prover-fixtures
```

After that completes, build `-p jolt --bin jolt` with the same environment/profile
but without Akita features. Set `JOLT_PATH` to that CLI for the profile run.

Logs: scratch parent `build-jolt-akita.log`, `build-jolt-akita-thin.log`,
`build-jolt-akita-nolto.log`, `build-jolt-ci.log`, `build-jolt-ci-prover.log`.
Do not relaunch a live build.
No protocol parameters were weakened. Future timings must name the CI profile
and loaded host; they are not directly comparable to the upstream M4 measurements.
