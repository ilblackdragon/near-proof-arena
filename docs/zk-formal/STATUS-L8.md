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
| Fast packed constraint evaluator (`eval.rs`) | L8 sub-agent | in progress |
| SHA-256 table (L5) trace gen + round trip + benchmarks | L8 sub-agent | in progress |
| Judge `prove` | L8 | blocked on L6 (NEAR AIR + witness→trace) |
| Verifier model / certificate in package | L4/L7 | placeholder reject-all model |

Blockers filed in `REQUESTS.md`: L1 `Fp.all`/`Fp8.all` computable (compiled
verifier OOMs at init); L4 compiled verifier ~quadratic in proof size
(13 s for a 0.5 MB proof; cap 10 s for ~4 MiB).

Benchmarks (8 threads, synthetic degree-4 table, no buses):

| table | prove | peak RSS | proof | Rust verify |
|---|---|---|---|---|
| 3000 cols × 2^17 rows (n0 = 2^21) | 39 s | 4.8 GB | 3.64 MiB | 0.09 s |

(before streaming: 70 s, 76 GB). Main costs: main commit 19.7 s (16 coset DFTs ≈ 12 s + WH leaf hashing,
16·T·W·4 bytes), openings 7.5 s (direct packed evaluation at the opened points),
quotient 8.9 s (scalar interpreter; packed evaluator pending).
