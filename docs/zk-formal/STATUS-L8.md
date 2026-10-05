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

Caveat: the worst-case domain (SHA table 2^22 × 544) would need ~18 GB in the
streaming prover; it is not in the workloads (DESIGN §8: only the Lean model
`P` must handle it).
