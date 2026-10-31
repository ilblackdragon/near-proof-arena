# Adversarial and realistic workload of a 1 Pgas chunk (PV86)

Status: research model, 2026-10-31. Numbers come from `model.py` (`python3 model.py`, the
"Workload" section of `model-output.txt`). Labels: **spec** = pinned nearcore parameter;
**M** = measured here; **MR** = measured earlier in this repo; **C** = cited; **D** = derived;
**A** = assumption.

## 1. Gas parameters

Source: pinned nearcore `/data/illia/nearproof-deps/nearcore`,
`core/parameters/src/snapshots/near_parameters__config_store__tests__85.json.snap`. That is the
config in force for protocol versions 85 up to 128, so PV86 included; the yaml diffs are
`res/runtime_configs/{parameters.yaml, 85.yaml}`.

* `regular_op_cost` = **822,756** (matches the Lean spec).
* `max_gas_burnt` = 1 Pgas, which is also the mainnet chunk gas limit. A 1 Pgas chunk therefore
  holds at most 1e15 / 822,756 = **1.215e9** Wasm operators.
* PV86 values that differ from the base yaml:
  * `contract_loading_bytes` = 1,089,295;
  * `ecrecover_base` = 278.8 Ggas;
  * `touching_trie_node` = `read_cached_trie_node` = 2.28 Ggas;
  * every BLS12-381 host is live, with its per-element prices;
  * `ml_dsa_65_verification_cost` = 100 Ggas (transaction costs).
* Size limits:
  * encoded witness ≤ 48 MiB and decoded ≤ 64 MiB;
  * contract-code response ≤ 64 MiB (`docs/evidence/lean-chunk-completion/size-limit-fixtures/`);
  * main storage proof soft limit 4,000,000 B; per-receipt storage proof 4,000,000 B;
  * combined transactions 4 MiB.

## 2. Circuit cost per primitive

Unit costs are given in two forms:
* for a 31-bit AIR: main cells `m` and bus fractions `f` (logUp/GKR);
* for a Binius64-style binary AIR: AND-constraint equivalents.

`model.py` turns each into INT32 operations per architecture (`ops_mf`, `ops_and`). "ops/gas"
is for architecture (a). "vs wasm" is relative to the worst Wasm operator.

| unit | gas/unit | max per Pgas | main cells | fractions | AND-eq | ops/gas (a) | vs wasm | source |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| contract-loading byte (SHA-256 code hash + PREP decode/validate/translate) | 1.09 M | capped at 64 MiB | 212 | 20 | 49 | 0.41 | **1.70** | SHA M (spike 3); PREP D (V3-PERF-DESIGN §3.4) |
| ripemd160 block, **as measured** (1,608 cols x 80 rows) | 680 M | 1.47 M | 128,640 | 160 | 960 | 0.255 | **1.05** | MR (HANDOVER); unoptimised layout |
| Wasm op: unaligned `i32.load` chain | 822,756 | 1.22e9 | 32 | 19 | 2,178 | 0.242 | 1.00 | M spike 4 / MR 1,452 AND/step x 1.5 (A) |
| Wasm op: `i64.div_u` chain | 822,756 | 1.22e9 | 30 | 18.5 | 2,178 | 0.234 | 0.97 | D from M |
| Wasm op: `i64.mul` chain | 822,756 | 1.22e9 | 22 | 14.5 | 2,178 | 0.181 | 0.75 | D from M |
| Wasm op: empty call | 822,756 | 1.22e9 | 30 | 12 | 1,452 | 0.169 | 0.70 | M |
| ML-DSA-65 verify (≈175 Keccak-f + ≈22 k mod-q products) | 100 G | 10,000 | 11.2 M | 66 k | 329 k | 0.155 | 0.64 | D sketch |
| storage write: touched trie node (verify old + hash new, ≤ 9 SHA-256 blocks each) | 2.28 G | 439 k | 192 k | 11 k | 10.8 k | 0.152 | 0.63 | D |
| storage read: touched trie node (9 blocks) | 2.28 G | 439 k | 96 k | 5.5 k | 5.4 k | 0.076 | 0.31 | D |
| keccak512 / keccak256 block | 2.64 / 2.92 G | 0.38 / 0.34 M | 63,192 | 0 | 624 | 0.03 | 0.12–0.13 | C Plonky3 keccak-air (2,633 cols x 24) |
| log byte (hashed into the outcome) | 13.2 M | 7.6e7 | 167 | 9.6 | 9.4 | 0.023 | 0.09 | D |
| memory.copy byte | 822,756 | 1.2e9 | 2.4 | 1.7 | 4 | 0.021 | 0.09 | M bulk16 |
| ed25519_verify (≈5,800 Fp25519 products + SHA-512) | 211 G | 4,750 | 609 k | 390 k | 1.9 M | 0.019 | 0.08 | D sketch |
| bls12381 map_fp2_to_g2 element (≈16,000 Fp381) | 900 G | 1,111 | 2.3 M | 1.6 M | 11.5 M | 0.018 | 0.07 | D sketch |
| ecrecover (≈6,500 Fp256) | 279 G | 3,587 | 624 k | 436 k | 2.1 M | 0.016 | 0.07 | D sketch |
| sha256 block | 1.54 G | 648 k | 10,675 | 612 | 600 | 0.013 | 0.05 | M (L5 layout) |
| bls12381 p2/p1 decompress, map_fp_to_g1, alt_bn128 multiexp, g2/g1 multiexp | 81 G–2 T | 500–12 k | — | — | — | 0.003–0.012 | 0.01–0.05 | D sketch |
| read_register → memory byte | 2.82 M | 3.5e8 | 2.4 | 1.7 | 4 | 0.006 | 0.03 | M |
| BLS / alt_bn128 pairings and sums, p256_verify | 5 G–5.1 T | — | — | — | — | ≤ 0.004 | ≤ 0.02 | D sketch |
| promise/receipt creation | 308 G | 3,250 | 55 k | 3.8 k | 3.5 k | 3e-4 | 0.00 | D |

Full table: `model-output.txt`.

### AIR sketches used above (D)

* **Non-native field multiplication**, 31-bit AIR (`nn_mul`):
  * 16-bit limbs, L = ⌈bits/16⌉;
  * columns a, b, c, q and 2L carries, so m = 6L;
  * f = 4L + 3: range lookups on c, q and the carries, plus 3 wiring fractions;
  * constraint degree 2;
  * 256-bit: 96 cells / 67 fractions; 381-bit: 144 / 99.
* **Non-native field multiplication**, binary AIR (`bin_nn_mul`):
  * 64-bit limbs; 2L² Binius64 MUL constraints for the product and the quotient product, plus 4L² carry ANDs;
  * MUL = 8 AND-equivalents (**A**).
* **Curve operation counts**, as non-native multiplications (my counts; ±2x):
  * ed25519 verify: two 253-bit scalar multiplications in extended twisted Edwards, two decompressions;
  * ecrecover / p256: R decompression plus a double scalar multiplication;
  * BLS12-381 pairing per element: Miller loop ≈ 5,000; the shared final exponentiation is charged to the base fee;
  * BN254 pairing: 10,000 per element;
  * G1 / G2 multiexp: double-and-add per element.

  These are D, not measured. None of them affects the verdict: the costliest curve family,
  `map_fp2_to_g2`, sits at 0.07x the worst Wasm operator per gas.
* **ML-DSA-65 verify** (FIPS 204, k = 6, l = 5):
  * ExpandA is 30 polynomials x ~5 SHAKE128 blocks;
  * μ, c̃ and SampleInBall add a few SHAKE256 blocks, so ≈ 175 Keccak-f in total;
  * 12 NTTs (z, c, inverse of 6) give ≈ 12.3 k products mod q = 8,380,417, plus 7.7 k pointwise
    and 1.5 k c·t1, so ≈ 22 k products in all;
  * each product's 46-bit result is decomposed in BabyBear (5 cells, 3 range fractions).

  Keccak dominates in the 31-bit AIR. ML-DSA can appear only as a transaction or action key,
  and the 4 MiB transaction limit caps it at ≈ 790 per chunk on the transaction side (≈ 5.3 KB
  per signed transaction). Gas caps it at 10,000.
* **Trie nodes**:
  * NEAR uses a SHA-256 Merkle-Patricia trie;
  * a branch node is ≤ 16 x 32 B plus a header, i.e. ≤ 9 blocks;
  * a write verifies the old node and hashes the new one;
  * each node touched costs `touching_trie_node` = 2.28 Ggas.

## 3. Witness authentication and other gas-free work

These are bounded by sizes, not by gas, so the adversary gets them on top of the gas budget:

* **Witness hashing**: ≤ 64 MiB decoded witness, i.e. trie nodes, incoming/source receipts and
  transactions:
  * every byte is SHA-256-hashed (1.05 M blocks);
  * every byte is parsed (16 main cells + 3 fractions per byte, **A**);
  * cost in (a): 2.3e13 INT32 ops ≈ 4 GPU-s at `eff` 0.35, about 8 % of the worst case.

  Below 1 Pgas the model scales this witness with gas, with a floor of 4 MiB, the storage-proof
  soft limit (`witness_scales`).
* **Contract code**:
  * distinct cold code is ≤ 64 MiB, the code-response cap;
  * loading it costs 64 MiB x 1.09 Mgas = 73 Tgas, which buys 64 MiB of SHA-256 code hashing
    plus PREP;
  * this is 1.70x the worst Wasm operator per gas, so the adversary always buys all of it;
  * repeated loads of the same code are prepared once, so no further gain.

  The earlier V3-PERF-DESIGN worst case (0.88 GB of distinct code from 210 contracts) predates
  the 64 MiB response cap. Under the cap, code loading is a 3e13-op add-on, not the binding case.
* Registers used as host inputs are consumed by reference. `value_return` bytes are bounded by
  the witness (V3-PERF-DESIGN §3.2), so neither adds an unpriced term.

## 4. The binding worst case

`adversarial()` proceeds greedily:
1. take the gas-free witness work;
2. buy the capped high-ratio units;
3. spend the remaining gas on the highest ops/gas unit for that architecture.

| arch | composition | INT32 ops | GPU-s at eff 0.35 |
|---|---|---:|---:|
| (a) univariate | 64 MiB witness + 64 MiB code (73 Tgas) + **927 Tgas of RIPEMD-160 blocks with the measured AIR** | 2.89e14 | 49.4 |
| (b) multilinear | witness + code + 927 Tgas of the unaligned `i32.load` chain (1.13e9 ops) | 2.56e14 | 43.8 |
| (c) binary | witness + 1 Pgas of Wasm ops (code hashing is cheap in binary) | 2.59e16 | 4,430 |

* **Binding operator: Wasm.** The unaligned `i32.load` chain is within ±5 % of the next
  candidates (`div_u` chain 0.97x, RIPEMD 1.05x). The ranking does not depend on it.
* **The measured RIPEMD-160 AIR is a cliff to fix, not a design point.** Its 128,640
  cells/block is 13.8x SHA-256, which makes RIPEMD the worst unit per gas in (a). A RIPEMD
  layout at ~2x SHA-256 (~20 k cells) would move it to ≈ 0.16x.
* The design rule from V3-PERF-DESIGN still holds: the worst *gas-priced* unit sets the per-gas
  rate, and no primitive is more than 1.05x the worst Wasm op. The exception is contract
  loading, which is capped by the 64 MiB code response.
* Curve and pairing hosts are 10–100x cheaper to prove per gas than Wasm. Their gas prices are
  generous for proving.

## 5. The realistic case

* **Measured mainnet distribution** (`bench/w13_gas.py`, shard 13, 1,223 chunks):
  * p50 0; p90 3.14 Tgas; **p99 18.45 Tgas**; max 115.3 Tgas;
  * 642 chunks burn zero gas.
* **Mix model** (`realistic()`):
  * 3.4 % of gas is Wasm operators (MR, corpus), at 0.55x the worst-op cost;
  * 30 % of the remaining host gas touches trie nodes (**A**);
  * witness = 8 MB per Pgas + 2 MB (**A**).

At p99 this is ≈ 1–3 GPU-s of total work, dominated by the ZK wrap, not the chunk (README). The
realistic chunk is ~50x below the 1 Pgas gas level and ~500x below the adversarial work.
