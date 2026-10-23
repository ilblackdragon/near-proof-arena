# Validation — 2026-10-21

Scope: `public-d0a/d0/00-h10004-s3`, 25 classical tables plus cached TAPE.
AIR SHA-256: `fa599b3b0c2dc786c295959ce92cfbbe73d74c4414b77979b436512a8ae3b452`.

* Clean isolated backend setup and locked release build passed.
* Witness trace generation passed (1,262,608 cells).
* All constraints and bus balances passed (4,245 distinct bus messages).
* Public values/messages recomputed from claim + hint match the witness preparation.
* Compact base proof: **459,984 bytes**, native verification passed.
* Saved base key/proof reloaded in another process and verified.
* Independently rebuilt base key from the AIR + public TAPE matches the entire saved key.
* A changed base-proof byte was rejected (`QueryPhasePoWInvalid`).
* First recursive proof: **374,105 bytes**, native verification and statement check passed;
  program 191,778 rows; trace shapes `(1048576,76), (1048576,83), (128,9), (65536,5)`.
* Checkpoint reload and statement check passed. The second layer generated a
  134,254-row padded program. Its proof passed verification at **374,563 bytes**
  in 430.23 seconds. L3 verified at **372,001 bytes** in 499.07 seconds;
  program 138,610 rows. L4 verified at **373,177 bytes** in 428.13 seconds,
  program 137,196 rows. L5 selected `bind=true`, preserving anchor M=3,
  and verified at **374,521 bytes** in 543.76 seconds. Its program-convergence
  and binding checks passed. FINAL verified at **299,935 bytes**.
* **FINAL packet: 299,967 bytes**, including the 16-byte hint and 16-byte framing.
  This passes the strict 300,000-byte gate by **33 bytes** for this measured fixture.
* Separate-process verification passed with claim/hint public reconstruction,
  restored extended-domain parameters, pinned setup hash, and program checking.
* Changed TAPE root, changed pinned program, corrupted proof, trailing bytes,
  truncated hint, and an untrusted setup pin were all rejected.
* Trusted setup: 3,711,888 uncompressed bytes, excluded from the packet; it is
  run-specific. This does not establish a uniform reusable setup or size bound.
* Final artifact and evidence are retained in
  `research/near-compression/results/pq-chunk-e2e/d0a-h10004-s3`.

Local artifacts/logs: `/data/illia/nearproof-deps/pq-chunk-e2e/runs/d0a-compact`.
The base used traces from `/tmp/nearproof-chunk-run-20261021/dump`, produced by the
same AIR and witness generator. The first layer used eight threads; checkpoint
continuation uses sixteen threads, CPUs `8-15,24-31`, memory cap 32 GiB.

Integration failures found and addressed:

1. The old base profile produced a verified 1,019,338-byte proof, whose verifier
   made a SHA trace exceeding the compact recursion profile. The base now uses
   compact WHIR parameters with the same 268-bit target and 2^30 interaction budget.
2. Cached TAPE must use full-height commitments when common-main traces use tight
   heights. The CPU base context and independent statement reconstruction now
   use the same explicit full-height commitment construction.
3. Backend VK serialization omits the extended-domain factor. Saved keys and
   final setup now preserve it explicitly across process boundaries.
4. Recursive program binding requires equal ALU domains. All recursive layers
   retain height 2^20. Later program capacity is 2^18; the earlier fixture's 2^17
   capacity was too small. Existing binding checks remain enabled.

This run does not validate a D3 state/Wasm join, arbitrary mainnet chunk shapes,
zero-knowledge masking, or the outstanding cryptographic security theorems.

Profiling is now enabled by default in `run.sh`. For the in-flight run, perf
attachment began during L2, so it does not cover base/L1 or the beginning of L2.
A 30-second diagnostic captured 5,191 samples with zero lost samples; 52.84%
of sampled cycles were in `fast_dft::dif_rows` during that interval. This is a
phase-specific observation, not a whole-run attribution. Continuous samples,
hardware counters, resource histories, and executable identity are retained
in `profile-chain/`. The profiler wrapper passed a CPU-workload smoke test with
nonempty samples, a hotspot report, and successful child exit-code propagation.

The completed attachment captured about 346,000 CPU-cycle samples with zero lost
samples, and peak process RSS 14.34 GiB. Corrected symbol attribution: DFT row
transforms 28.31%, memory copies 20.08%, SHA-384 batch routines 22.76%. The binary
path was rebuilt during capture; `perf-symbols.data` repairs the build ID using
the preserved running executable, leaving sample count and event totals unchanged.
Future captures use `--buildid-mmap`. Compilation briefly overlapped the run,
so these timings are diagnostic, not a controlled optimization comparison.
