# STATUS — lane L8 (Rust prover `np-udr-stark`, conformance, package)

Crate: `examples/np-udr-stark/source` (standalone cargo workspace, Plonky3
rev 3acc8b7: p3-baby-bear/field/dft/matrix/util only). Package:
`examples/np-udr-stark/` (candidate.toml native-lean, reproducible build).

| Item | Owner | State |
|---|---|---|
| Field/encodings, `decodeChal`/`decodeOod` (= L1 `Algebra/Decode`) | L8 | done |
| `H`/`WH`, tags 0x00–0x05 (FORMATS v1 rev) | L8 | done |
| Transcript (`u8 #roots ‖ roots ‖ clear`, CHAL steps state, le32 queries) | L8 | done |
| MMCS mixed heights, rows inlined in NODE; streamed leaf hashing | L8 | done |
| Multiproof wire format (interleaved, FORMATS §5) + parser | L8 | done |
| AIR import/export `np-air-v1` (byte-identical with `Air.exportJson`) | L8 | done |
| Quotient (2^⌈log nq⌉ coset blocks), DEEP-ALI, shared batching vector | L8 | done |
| Grand-product aux (power/partial-product chains, running products, finals) | L8 | done |
| FRI (binary folds, arity ≤ 8 commits, roll-ins before commit, final deg < 2) | L8 | done |
| Rust reference verifier (mirrors `Stark/{Bcs,Protocol,Verifier}.lean`) | L8 | done |
| Proof-mutator tests (Rust verifier; 7k bit flips, trunc/extend, claim/pub) | L8 | done |
| **M1: round trip with compiled Lean verifier** (fib, multi-height, buses) | L8 | **done** (needs L1 `noncomputable Fp.all` locally) |
| Lean conformance harness `conformance/run.sh` (export equality, accept, mutants) | L8 | done |
| Fast packed constraint evaluator (`eval.rs`, BlockEval) | L8 | done |
| Random-point constraint differential Lean vs Rust (`np-lean-eval`) | L8 | done (fib, multi, bus) |
| SHA-256 table (L5 `Table.table`) + byte/digest companions: Rust trace gen = Lean `Gen` cell for cell; AIR export byte-identical; Lean verifier accepts, mutants rejected | L8 | done |
| Judge `prove` | L8 | blocked on L6 (NEAR AIR + witness→trace) |
| Verifier model / certificate in package | L4/L7 | placeholder reject-all model |

Blockers filed in `REQUESTS.md`: L1 `Fp.all`/`Fp8.all` computable (compiled
verifier OOMs at init); L4 compiled verifier ~quadratic in proof size
(13 s for a 0.5 MB proof; cap 10 s for ~4 MiB).

Benchmarks (8 threads, synthetic degree-4 table, no buses):

| table | prove | peak RSS | proof | Rust verify |
|---|---|---|---|---|
| 3000 cols × 2^17 rows (n0 = 2^21) | 33 s | 4.8 GB | 3.64 MiB | 0.09 s |

(before streaming: 70 s, 76 GB). Main costs: main commit 19.7 s (16 coset DFTs ≈ 12 s + WH leaf hashing,
16·T·W·4 bytes), openings 7.5 s (direct packed evaluation at the opened points),
quotient 3.7 s (packed AVX2 BlockEval, 7.9x the scalar tape; the rest is the 4 block DFTs).

SHA-256 toy (L5 table 544 cols + byte table 4 cols at 4× height + digest table; 1000-byte messages; 8 threads):

| SHA rows | blocks | prove | peak RSS | proof | Rust verify | Lean verify |
|---|---|---|---|---|---|---|
| 2^12 | 240 | 0.45 s | 171 MB | 1.45 MB | 22 ms | 180 s |
| 2^14 | 960 | 2.16 s | 675 MB | 1.67 MB | 27 ms | 230 s |
| 2^16 | 3840 | 8.9 s | 2.7 GB | 1.92 MB | 25 ms | – |
| 2^17 | 7680 | 17.6 s | 5.3 GB | 2.07 MB | 26 ms | – |

Lean (compiled) verify is the blocker for the 10 s verify cap (REQUESTS.md, L8 → L4).

## lane/zk-L8b (off lane/zk-int + lane/zk-L4e)

* `minQueryLog = 8`: Rust schedule rejects `n0 < 8` (prover error asks to pad the
  largest table to ≥ 16 rows); `fit32` is the identity for SHA-256 (documented).
* `npudr bench <w> <log> [tables] --out <dir>`; `run.sh` takes logs ≥ 4 (default
  4 6 10) and `BENCH="w:log[:tables] …"` for Lean-verify timings.
* With L4d's linear-time verifier and L1's `noncomputable` fix (both in zk-int),
  `BENCH="1000:14 3000:14 1000:16:3 3000:17" ./run.sh 4 6 10` → ALL PASS, no local
  patches needed:

| proof | size | Lean verify |
|---|---|---|
| bus 2^10 | 0.50 MB | 105 ms |
| SHA toy | 0.92 MB | 198 ms (was 83 s) |
| bench 1000 × 2^14 | 1.58 MiB | 350 ms |
| bench 3000 × 2^14 | 3.35 MiB | 1029 ms |
| bench 3 × 1000 × 2^16 | 3.77 MiB | 2028 ms |
| bench 3000 × 2^17 | 3.64 MiB | 887 ms |

## lane/zk-L8c — real NEAR prover (`out/prove`)

`prove` = request/witness → claim (reexec engine, = NearSpec `deriveClaim`) →
`npudr::near` (cell-for-cell port of L6 `Near.render (extOf c w)` + L5 SHA) →
`np-udr-stark-v1` over `nearAir` (`source/near-air.json` = Lean
`Air.exportJson nearAir`, byte-identical).

`bench/near-bench.sh` (8 threads, heavy wrapper; results
`bench/results/near-2026-10-05.tsv`): all 20 public fixtures + 18 oracle-generated
class workloads (seed 7, profiles basic/prefix/boundary/repeat/prices/large):
**claim == expected_claim, Rust verify accept, compiled Lean verifier accept on all 38.**

| class | prove | peak RSS | proof | Lean verify |
|---|---|---|---|---|
| batch-1 | 0.24–0.29 s | 22 MB | 1.84–1.92 MB | 450–503 ms |
| batch-16 | 0.9–1.4 s | 117–144 MB | 2.30–2.47 MB | 579–647 ms |
| batch-256 | 14.1–16.1 s | 1.77–1.93 GB | 2.86–3.05 MB | 768–1146 ms |
| caps | 600 s | 16 GiB | 8 MiB | 10 s |

Trace cross-check: Rust `npudr nearrender` == Lean `np-lean-render` (claim, all SHA messages, all 7 tables) byte-identical on all 38 cases; `nearcheck`: 0 violations, 0 bus imbalance (no L6 bug).

Caveat: the worst-case domain (SHA table 2^22 × 544) would need ~18 GB in the
streaming prover; it is not in the workloads (DESIGN §8: only the Lean model
`P` must handle it).

## lane/zk-L8d — no panics, low-memory prover, reproducible package

* **Errors, not panics** (sub-agent, lane/zk-L8d-gen): `near::prepare(_cols)` returns `Err`
  on every out-of-domain input (domain guard, height check, trie depth guard); `prove`
  runs under `catch_unwind` on a 1 GiB-stack thread and writes outputs atomically only
  on success (exit 2, nothing written otherwise). `tests/near_fuzz.rs`: 12,000 random
  fixture mutations + 21 structured out-of-range cases, 0 panics.
* **Low-memory prover** (`prover.rs`; the previous one is `prover_ref.rs`; proofs are
  byte-identical, `tests/lowmem.rs`, including tiny budgets): compact column traces
  (`cols.rs`, generators produce them directly: `near::prepare_cols`), aux columns
  recomputed, streaming wide-hash commitments with recomputed low Merkle levels
  (`lmcommit.rs`), budgeted multi-pass quotient with rolling next-row ranges, OOD/DEEP
  from H values, copy-free FRI. Budget `NPUDR_MEM_GB` (default 11).
* **Max in-domain witness** (`npudr gen-max`: n = 256, revealedBytes 2,999,955; sha and
  node tables 2^22 rows): claim == derived claim, Rust verifier accepts,
  **peak RSS 11.4 GB (≤ 12 GiB)**, proof 3.56 MB — but **prove 1742 s** (8 threads,
  AVX2), over the 600 s cap: quotient 1170 s (aux-column recomputation 434 s, per-pass
  iDFTs), main commit 206 s, aux 164 s, openings 100 s. Old prover: ~55 GB, not runnable.
* Class workloads unchanged in outcome (38/38 claims, Rust accept); batch-256 13.2–14.1 s,
  ≤ 1.57 GB (`bench/results/near-lowmem-2026-10-05.tsv`).
* Reproducible package build with the real prove: two clean builds (fresh HOMEs, second
  under `unshare -rn`) bit-identical: prepare 6ba6ebb6…, prove e7a9eb09…, verify c82117cb….

## lane/zk-L8e — max witness under 600 s (prover-only child `np-udr-stark-fast`)

Max in-domain witness (gen-max, sha/node tables 2^22, 3.3 GB compact trace), all
runs pinned to CPUs 8-15 (CCD1, no V-cache; the live worker owns 0-7/16-23),
proof byte-identical to the main prover's (sha256 0fc29afc…) in every run:

| prover | threads | prove | peak RSS |
|---|---|---|---|
| main (L8d), CPUs 0-7, busy host | 8 | 1859 s | 11.4 GB |
| L8e, AVX2 build | 8 | 627 s | 11.1 GB |
| L8e, AVX-512 build | 8 | 394 s | 11.25 GB |
| L8e, AVX-512 build (SMT siblings 8-15,24-31) | 16 | 383 s | 11.5 GB |
| packaged `out/prove` (dispatches to `out/prove-avx512`) | 8 | **379 s** | 11.27 GB |

Lean `out/verify` accepts the max-case proof (1.0 s). Phases (AVX-512, 8 thr):
main commit 153 s, aux 68, quotient 89, quot commit 25, OOD 9, DEEP 18, openings 28.

* Quotient (1241 s → 89 s): it already ran on 2^⌈log nq⌉·T = 4T points; the cost was
  re-transforms. Now: values on nq = 3 cosets + per-coefficient Vandermonde solve;
  main trace converted to coefficients once (compact columns released, rebuilt
  after); bus family from cached aux coefficients and, for table 0, the 99
  degree-1 interaction-value polynomials instead of the 403 columns they read;
  base-field fingerprints (FastBus).
* Aux values computed once per row for all groups (was once per 32-column chunk),
  aux coefficients cached across commit groups; glibc mmap threshold pinned +
  malloc_trim (quotient peak 13.7 → 11.1 GB); KEEP 4 → 6.
* AVX-512: the arena Firecracker guest exposes AVX-512 F/BW/DQ/VL/IFMA (no CPU
  template; verified by running ZMM code in an arena-launched guest). `out/prove`
  (x86-64-v3) execs `out/prove-avx512` (x86-64-v4, same source) after runtime
  detection (`NPUDR_NO_AVX512=1` disables). The packed Montgomery multiply-add is
  ~6.6× faster (opening folds), coset DFTs ~1.5×. AVX2-only hosts: ~620 s, over cap.
* Package `examples/np-udr-stark-fast` (parent `examples/np-udr-stark` unchanged =
  main): two clean builds (second `unshare -rn`) bit-identical; `out/prepare`
  6ba6ebb6… and `out/verify` c82117cb… identical to the parent, formal tree and
  dependency-locks identical; `out/prove` 40ad5fb5…, `out/prove-avx512` 4cb43664….
  `parent = "sub_…"` must be set to the admitted np-udr-stark submission.
* Fixtures with the packaged binaries: 38/38 claims, 38/38 accept, all false-claim /
  mutated / truncated / swapped rejected; batch-256 prove ~7.6 s (was 13–14 s).
* Tests: `tests/lowmem_near.rs` (new): ref == lowmem on NEAR fixtures v4/v5/v17 and
  gen-max 60k at default and tiny budgets; toy `lowmem`, `near_fuzz` pass; under
  both AVX2 and AVX-512 builds.
* Workload spec: `near-arena-oracle gen --profiles max_witness` (oracle/src/maxwit.rs)
  + `spec/workloads/near-transfer-receipt-v2/max-witness.{json,md}` (not governed;
  pinned spec doc unchanged).

## lane/zk-L8f — np-udr-stark-fast2 (prover-only child of sub_19cc9c90…)

Live: np-udr-stark-fast (sub_56bb976b…) regressed small classes (batch-1 3.05 s vs
parent 1.99, batch-16 9.14 vs 6.49; batch-256 48.7 vs 62.2). Reproduced with the
worker's real BENCHMARK stage (`bench_session`, Firecracker, 8 vCPUs, CPUs 8-15):
parent 2.25 / 7.36 / 72.4 s, fast 3.45 / 11.18 / 65.1 s (+ CACHING_SUSPECTED).

Per-invocation profile in an arena-launched VM (`bench/pfvm.sh`; batch-16 request,
parent 0.87 s vs fast 1.32 s): openings 0.20 → 0.79 s (KEEP 6: 64-leaf subtrees per
query) and main commit 0.11 → 0.15 s (pinned glibc mmap threshold: page faults on
every ≥1 MB allocation); the AVX-512 dispatch fires in the guest (fake sibling
returned rc 3) but gains nothing at these sizes.

fast2 = fast's prover with size-dependent strategies (memory-saving paths only when
the largest table's coefficients exceed 1/4 of the budget / 70% would be exceeded),
block-wise opening evaluation for T ≤ 2^13, parallel subtree hashing; AVX-512
dispatch dropped (single AVX2 binary). Proofs: 27/27 byte-identical to the parent
(24 generated class requests + fixtures v4/v5/v17), toy/NEAR identity tests (both
strategies), fuzz; max witness identical (0fc29afc…), 11.27 GB, 381 s uncontended
(AVX2). Package: two clean builds bit-identical; prepare 6ba6ebb6…, verify c82117cb…,
build recipe and formal tree identical to the parent; prove 872716f6….

| class (8 requests, one VM per batch, CPUs 8-15) | parent | fast2 |
|---|---|---|
| per-request, quiet host (`pfvm.sh`, 4 requests) batch-1 | ~230 ms | ~125 ms |
| batch-16 | ~810 ms | ~490 ms |
| batch-256 | ~7.97 s | ~5.96 s |
| paired batches, contended host (min of rounds) batch-1 | 2.24 s | 1.29 s |
| batch-16 | 7.76 s | 5.11 s |
| batch-256 | 94.5 s | 66.9 s |

fast2 won 14/16 paired batches. The local fast2 `bench_session` ran under heavy
interference from other lanes on CPUs 8-15/24-31 (fresh-only medians 1.82 / 5.28 /
73.1 s with MADs up to 12 s; its warm-ups were 1.34–1.40 / 4.30–4.40 / 53.6–54.1 s).

CACHING_SUSPECTED: the tripwire compares a *different* batch (fresh-confirm) with
the steady-state median of one fixed batch; it trips when the fresh batch is > 5%
and > 5·MAD slower. Each batch runs in a fresh VM and the prover keeps no state
(no files written outside the claim/proof outputs). The parent's own fresh batch-1
was already +6.0% (saved only by its 35 ms MAD); a faster, more deterministic prover
has a smaller MAD, so ordinary input-size variation between batches trips it.

Correction to L8e: `~/.cargo/config.toml` sets `[target.x86_64-unknown-linux-gnu]
rustflags`, which overrides the project's `build.rustflags`, so local "AVX2" dev
builds were plain x86-64 (SSE2). The L8e "AVX2-only ≈ 620 s" and "AVX-512 6.6× on
folds" compared against SSE2; a real AVX2 build proves the max witness in 381 s.
Packaged builds (fresh HOME, build.sh flags) were always AVX2.

Judge-verify with the packaged fast2 binaries: 11/11 cases claim ok, accept, and
false-claim / mutated / truncated proofs rejected; the sweep was stopped at the
12th case because the shared `zkbuild.slice` sat at its 40 GB memory.high (other
lanes), throttling every process in it (also the cause of the contended timings
above). Proofs being byte-identical to the admitted parent's covers the rest.
