# stark-plonky3: custom Plonky3 STARK with hand-written AIRs (EXPERIMENTAL)

This candidate targets `near/pv86/receipt-transfer-batch/v0`
(`chl_5ef2bc7d2068219635426e47ca46bfbb`; `spec/claim-v1.md`,
`spec/near-transfer-receipt-v1.md`). It is the third backend family, next to
transparent re-execution (`examples/reexec-witness`) and a zkVM
(`examples/zkvm-sp1` on `lane/backend-zkvm`): a **custom STARK**. The relation is
written directly as nine AIR tables and proven with
[Plonky3](https://github.com/Plonky3/Plonky3) `p3-batch-stark` at rev
`3acc8b70e68d6c2afc03930700c26540bd47458d`. The proof contains no witness
bytes. `verify` is a native Rust binary (`verify_route = "native"`).

**Tier expectation: EXPERIMENTAL.** No formal obligation about the AIR, the
proof system or the Rust verifier is discharged. `formal/` deliberately
defines no `Candidate.certificate`, so the judge must report
`CERTIFICATE_MISSING`. The estimated soundness bound is also below the
profile's target under the profile's own accounting (see
[Security](#security-parameters-and-honest-bounds)). See
[`EVIDENCE.md`](EVIDENCE.md) for the obligation-by-obligation matrix.

## Headline numbers

All numbers are local, not judge-measured. Host: AMD 9950X3D. Each
process was pinned to 8 CPUs (`taskset -c 0-7`), as in the challenge
hardware profile. The host was shared, with load average 11–24.

| class | prove / request (median) | batch of 8 (median) | prove peak RSS | proof bytes | verify | verify RSS |
|---|---:|---:|---:|---:|---:|---:|
| batch-1 | 0.29 s | 2.34 s | 85 MB | 7.14 MB | 230 ms | 41 MB |
| batch-16 | 0.36 s | 2.97 s | 222 MB | 7.14 MB | 240 ms | 41 MB |
| batch-256 | 0.95 s | 7.64 s | 1.26 GB | 7.14 MB | 290 ms | 41 MB |

Workloads: `near-arena-oracle gen --seed 9001 --valid 8 --receipts {1,16,256}
--fixtures-layout`, the same generator and seed the reexec lane used. Raw data:
`bench/results-2026-10-03/measure-workloads.tsv`, produced by
`bench/run-bench.py` (1 warm-up and 5 timed rounds per class, one fresh
process per request).

* **Correctness.** Claims are byte-identical to the oracle's `expected_claim`
  on all 20 public fixtures and on 24 workload requests. They also match on
  1502 generated in-domain cases (oracle `gen --seed 4242`). On every one of
  these cases the generated traces satisfy every AIR constraint and balance
  every bus, checked natively.
* **Out-of-domain inputs.** The 210 generated out-of-domain cases and the 14
  rejection fixtures are all refused by the prover. Separately, when the
  prover is *forced* to build a witness for them, the AIR or the verifier's
  static claim checks reject it (see [Conformance](#conformance)).
* **Adversarial proofs.** The arena's `proof-mutators` produced 360 hostile
  proofs over 9 cases. Our structure-aware mutator produced 232 field-level
  proof mutants across 22 field patterns, plus 1236 claim byte flips and
  cross-case claim/proof swaps. Every one was **rejected**.
* **Under-constraint probe.** 422,319 single-cell perturbations of honest
  traces, covering every non-multiplicity column of every table on 8 cases.
  **0 went undetected**. This is tested coverage of one class of
  perturbation, not a proof.
* **`arena check-local`.** All local gates pass: PKG_WELLFORMED,
  BUILD_REPRODUCIBLE, CONFORMANCE_DIFFERENTIAL, PROVER_RELIABILITY,
  ADVERSARIAL_PROOFS and RESOURCE_LIMITS
  (`bench/results-2026-10-03/arena-check-local.txt`).

### Comparison with the other two families (same statement)

| | reexec-witness (reference) | **stark-plonky3 (this)** | zkvm-sp1 |
|---|---|---|---|
| proof system | none (witness = proof) | Plonky3 batch-STARK, hand-written AIR, KoalaBear⁸, FRI, LogUp | SP1 v6.8.1 RISC-V zkVM, recursion-compressed STARK |
| prove / request | ≈ 0.4 ms (batch medians 3.5 / 3.5 / 4.4 ms per 8 requests, reexec lane's `measure_provers.py`) | 0.29 / 0.36 / 0.95 s | 46–110 s (2–28 receipts), 58–220 s (117–256 receipts) |
| prove peak RSS | 2 MB | 85 MB – 1.26 GB | 16–38 GB |
| proof bytes | 0.5–1 KB / 4.8–6.8 KB / 59–70 KB (linear in witness) | **7.14 MB** (≈ constant) | 1.27 MB (constant) |
| verify | ≤ 10 ms / ≤ 10 ms / 150 ms (this run) | 230–290 ms | 30–110 ms |
| witness revealed | yes | no (validity only, ZK not claimed) | no |
| crypto assumptions | SHA-256 CR | SHA-256 CR + SHA-256 as random oracle (**both approved by the profile**) | Poseidon2 RO, BLAKE3 (not approved) |
| verifier TCB | Lean kernel + Lean compiler (native-lean route) | ≈ 3.9 k LOC ours + Plonky3 verifier crates (≈ 70 k LOC incl. tests) | ≈ 10–15 k LOC sp1-verifier + recursion circuits |
| formal status | admission certificate | none (EXPERIMENTAL) | none (EXPERIMENTAL) |

The reexec and SP1 numbers come from those lanes. Our timer resolution for
reexec was 10 ms. The SP1 numbers were measured on 32 cores on a shared host.

## Design

### Tables and buses

One proof covers nine AIR instances, committed together and opened with one
FRI proof. The instances are linked by LogUp buses (`p3-lookup`). On every
bus, a message is identified by the **pair** `(kind, index)`, held as two
separate tuple entries; the reason is in [EVIDENCE.md](EVIDENCE.md),
"soundness review".

| table | one row = | main cols | constraints | max deg | bus interactions / row | role |
|---|---|---:|---:|---:|---:|---|
| `sha` | one SHA-256 compression | 7803 | 8375 | 3 | 67 | compression (Plonky3 `sha256-air` constraints, vendored) + FIPS 180-4 padding + block chaining + digest |
| `rcpt` | one receipt | 1084 | 3017 | 9 | 1252 | borsh layouts of receipt / outcome / leaf / refund-id / refund receipt; account-id grammar, `system`, named receiver; gas and u128 arithmetic; amount chain |
| `mrk` | one outcome-merkle node | 82 | 207 | 5 | 70 | nearcore `merklize` shape (odd promotion) |
| `sort` | one receipt id, sorted | 97 | 239 | 5 | 33 | ids strictly increasing, so pairwise distinct |
| `acct` | one touched account | 352 | 731 | 9 | 343 | AccountV1 value pre/post, key nibbles of `0x00‖id`, walk end, value slot |
| `node` | one revealed trie node | 1381 | 3053 | 9 | 1446 | `RawTrieNodeWithSize` pre/post serialization, child/value windows, walk edges, witness-size bound |
| `path` | one key nibble of one account | 14 | 45 | 3 | 4 | the trie walk root → value slot |
| `byte` | 256 fixed rows | 3 | 5 | 2 | 3 | range-8, char class, nibble split (preprocessed) |
| `r12` | 4096 fixed rows | 1 | 3 | 2 | 1 | range-12 (preprocessed) |

Buses (`source/src/consts.rs`):

* Permutation buses (multiset equality): `bytes (kind, msg, pos, byte)` from
  producers to the SHA table, `chain`, `mem (k, t, amount)` (offline memory
  argument for repeated receivers), `rids`, `keynib`, `final`, `vslot`.
* Lookup buses (free provider multiplicities): `digest (kind, msg, limbs)`,
  `range8`, `range12`, `class`, `nib`, `acct`, `mpos`, `edge`, `eps`.

**Public values** are the 232 fixed-width bytes at the end of `claim.bin`
(`shard_id` … `tokens_burnt_total`), one field element per byte. `verify`
checks the rest itself: strict decoding, format/statement tags, protocol
version 86, `mainnet`, `1 ≤ n ≤ 256`, `(n−1)·G < gas_limit`, and
`gas_burnt_total = n·G`.

How each part of the relation (`spec/near-transfer-receipt-v1.md` §2–§4) is
enforced:

* **`receipts_commitment`.** RCPT emits `u64 shard_id ‖ u32 n` from the
  public values. Each row then emits its receipt's exact borsh bytes at a
  running offset `o`. The offsets are linear in the string lengths and the
  key type. The SHA chain of message `(K_RC, 0)` must receive exactly these
  bytes, and its digest must equal the public `receipts_commitment`.
* **Receipt shape.** The constants `ReceiptEnum::Action = 0`, the three
  `u32` counts `0, 0, 1` and `Transfer = 3` are emitted as constants, so no
  other shape can be hashed. The key type is boolean, with 32/64-byte keys.
* **Account ids.** For predecessor, receiver and signer: a class lookup
  per char, length 2..64, no leading, trailing or doubled separator. The
  predecessor is not `system`: a sum of squares of small integers, made
  non-zero by an inverse witness. The receiver is named: not 64-hex and not
  `0x`/`0s` + 40 hex, using the same inverse technique.
* **Gas.** `hr = [gas_price > block_gas_price]` with a range-checked
  difference `D` (non-zero when `hr`). `p = min(...)`. `burnt = G·p` and
  refund amount `G·D` use a byte convolution with range-checked carries and
  no overflow. `tokens_burnt_total` is a running byte-wise sum with no
  carry-out. `refund_count` is a running count.
* **Outcomes.** The `PartialExecutionOutcome`, the leaf
  `u32 2 ‖ id ‖ H(outcome)` and the refund-id preimage `id ‖ height ‖ 0` are
  emitted per row. MRK reproduces `merklize` level by level from `n`, and
  its root digest must equal the public `outcome_root`.
* **Refunds.** The refund receipt (`system` → signer, refund id, signer key,
  amount) is emitted into `(K_RF, 0)` at running offset `o2`, behind the
  `u32 refund_count` header. Its digest must equal the public
  `refunds_commitment`.
* **Balances.** Each receipt reads `(k, t_prev, before)` and writes
  `(k, r+1, after)` on the `mem` permutation bus, with `t_prev ≤ r`. ACCT
  writes `(k, 0, pre)` and reads `(k, t_last, post)`. Because every write is
  consumed exactly once and reads are time-bounded, each receipt reads the
  latest earlier write. Every step checks `after = before + deposit` with no
  overflow, `after ≠ u128::MAX`, `after + locked < 2^128`, and either
  `storage ≤ 770` or `after + locked ≥ 10^19·storage`. The pre-state amount
  must not be `u128::MAX` (AccountV1).
* **Trie.** NODE serializes every revealed node twice, once per state. Child
  and value windows carry child pre/post digests (`digest` lookups). Node 0
  must hash to the public `pre_state_root` and `slice_post_root`. PATH walks
  each account's key nibbles from `(0, 0)` along edges that the nodes
  derive from their own bytes: branch child slots, hex-prefix key nibbles,
  and extension → child epsilon moves. The walk must end at a touched value
  slot. Each slot is offered exactly once (`vslot`), with `len = 72`, pre
  window = `H(value_pre)` and post window = `H(value_post)`. The sum of
  revealed bytes must be ≤ 3,000,000 (`witness_size`).
* **Distinct ids.** SORT holds the receipt ids received from RCPT in
  strictly increasing order.
* **SHA-256.** Data bytes are read from the compression's message-schedule
  bits, so every byte any producer emits is range-checked. Padding is forced
  to the standard minimal form: `0x80` right after the data, zeros, and the
  big-endian bit length in the last block. Blocks chain through a permutation
  bus. The first block of a message must contain data, so no "empty"
  shadow chain can exist.

### Prover and verifier

```text
prepare --params p.bin --out pub/   public.bin = tag ‖ statement ‖ sha256(params) ‖ AIR/config digest
prove   --public pub/ ...           native re-execution (refuses out-of-domain, exit 3) → witness → 9 traces
                                    → multiplicities → p3-batch-stark prove → proof.bin
verify  --public pub/ --claim c --proof p
        public.bin digest == digest of the AIR compiled into this binary   (else exit 2)
        strict claim decode + static domain checks                           (else exit 1)
        proof ≤ 8 MiB, tag, postcard decode, no trailing bytes,
        per-table height caps, Plonky3 verify_batch (panics caught)          (else exit 1)
```

* `proof.bin` = `bytes "np-stark-plonky3-proof-v1" ‖ postcard(BatchProof)`.
* The **AIR/config digest** is SHA-256 over: the configuration description
  (field, extension, hashes, every FRI parameter, the transcript domain
  separator, the Plonky3 rev); per table, its name, widths, public-value
  count, lookup budget and preprocessed trace; and a **Schwartz–Zippel
  fingerprint**. The fingerprint evaluates every constraint and every bus
  interaction once at a fixed pseudo-random point in KoalaBear⁸
  (`source/src/fingerprint.rs`). Computing it takes 4 ms. The digest
  identifies the constraint system as polynomials. It does *not* bind the
  verifier's code (see EVIDENCE row IMPL).
* Hostile inputs cannot crash `verify` into an accept: panics become exit 1
  (`catch_unwind`), the proof size is capped before decoding, and the
  degree bits are checked against per-table caps before any work.

## Security parameters and honest bounds

| parameter | value |
|---|---|
| field / challenges | KoalaBear `p = 2^31 − 2^24 + 1`; degree-8 binomial extension (≈ 248 bits) |
| commitments / Fiat–Shamir | **SHA-256 only**: leaf `SerializingHasher<SHA-256>`, node `SHA-256(l ‖ r)` (full hash, with padding), transcript `HashChallenger<SHA-256>` with domain `near-arena/stark-plonky3/v1` |
| FRI | rate 1/8 (`log_blowup = 3`), binary folding, final poly degree 0, **104 queries**, **20-bit** query PoW |
| LogUp | single `(α, β)` pair over the extension; Plonky3 enforces the multiplicity height bound `Σ wᵢhᵢ < p` |

Bounds come from Plonky3's own security calculator (`p3-security` /
`uni-stark` `ProvenSecurity` / `ConjecturedSecurity`, unverified f64 code).
It was run per table on the real shapes, with the batch-wide count of
batched functions, the LogUp term (`N(W+2)/|EF|`) and a union bound over
tables (`source/src/security.rs`, `bin/seccalc.rs`; raw output in
`bench/results-2026-10-03/security-calculator-*.txt`).

| bound (bits) | per proof, SHA-256 CR cap (128) | round-by-round, cap lifted | arena profile accounting, q_H = 2^64 |
|---|---:|---:|---:|
| proven, unique-decoding regime (2024/1553 Thm 2; BCIKS20 UDR proximity gaps) | **102.5** | 102.5 | **38.5** |
| proven, Johnson / list-decoding regime (2024/1553 Thm 3 + DKT26 line-MCA) | 128 | 171 | **107** |
| conjectured (2025/2010 random-words) | **128** | 215 | 128 |
| LogUp fingerprint term | – | 221.8 | – |

The profile accounting is `Adv ≤ (q_H + 1)·ε_rbr + q_H²/2^256`
(`security/README.md`: with q_H = 2^64 a bound of 2^-128 needs per-query
error ≤ 2^-192).

Honest reading:

* **Conjectured security reaches 128 bits.** It is capped by SHA-256
  collision resistance, and holds even under the profile's q_H = 2^64
  accounting.
* **Proven security is below 128.** In the classical unique-decoding regime
  it is **102.5 bits per proof**. This is the regime whose proximity-gap
  lemma is formally proven in ArkLib (BCIKS20 UDR); FRI soundness itself is
  not proven anywhere in Lean. Under the profile's FS accounting it is only
  38.5 bits. The Johnson-regime bound rests on recent results (DKT26,
  2026/2056) and reaches 128 bits per proof, but only 107 bits under the
  profile accounting. **Even with every formal obligation discharged, this
  parameter set would fail `SECURITY_BOUND_INSUFFICIENT`.**
* Changing parameters is limited by proof size. The proof is 7.14 MB, 85% of
  the 8 MiB `max_proof_bytes`. It is dominated by LDE openings: about 50 KB
  per query for the main trace and about 20 KB per query for the rest.

Cost tradeoff (query count `q`, query PoW 20; proof ≈ 0.4 MB + 65 KB·q):

| q | proof | proven UDR | proven LDR | conjectured | UDR / LDR / conj under q_H = 2^64 |
|---:|---:|---:|---:|---:|---|
| 40 | ≈ 3.0 MB | 49.8 | 75.8 | 128 | –14 / 12 / 71 |
| 64 | ≈ 4.6 MB | 69.5 | 111.5 | 128 | 5.5 / 48 / 128 |
| **104 (chosen)** | **7.14 MB** | **102.5** | 128 | 128 | 38.5 / 107 / 128 |
| 128 | ≈ 8.7 MB (over cap) | 122.5 | 128 | 128 | 58.5 / 128 / 128 |
| 240 | ≈ 16 MB | 128 | 128 | 128 | 128 / 128 / 128 |

We chose q = 104 because it is the smallest query count with **proven
(unique-decoding) ≥ 100 bits** that still fits the proof-size cap.
Profile-grade proven security (LDR ≥ 128 under q_H = 2^64 needs q ≥ 128; UDR
needs q ≈ 240) needs a narrower trace first. The SHA table is 52% of the
width. A two-rows-per-compression SHA layout would roughly halve it and allow
q ≈ 150 within 8 MiB. Raising the PoW instead costs prover time
(24 bits added ≈ 150 ms).

## Conformance

`npdev conform <dir>` checks, for every case, natively without the STARK:
the claim equals `expected_claim`, and the generated traces satisfy every
constraint and every bus. For out-of-domain cases the prover must refuse.
Then a witness is built anyway, with domain checks off and wrapping
arithmetic, and the verifier's static claim checks or the AIR must reject
it.

| set | result |
|---|---|
| public fixtures (20) | 20 in-domain ok |
| workload classes (24) | 24 in-domain ok, all proved and verified |
| oracle `gen --seed 4242` (1502 in-domain) | 1502 claims byte-identical + AIR satisfied |
| same, 210 out-of-domain (14 families × 15) | all refused by the prover. Forced witnesses: rejected **by the AIR** for balance_overflow, sentinel_balance, storage_stake, tokens_burnt_overflow, implicit_receiver, system_predecessor (`rcpt`) and duplicate_receipt_id (`sort`). Rejected by the verifier's static claim check for gas_limit and wrong_protocol_version. Not representable in the AIR for account_v2 (value ≠ 72 bytes), receiver_missing (no trie path), multi_action, non_transfer_action and empty_batch |
| rejection fixtures (14) | same pattern, one per family |

## Layout

| path | what |
|---|---|
| `source/src/air/` | the AIRs: `sha.rs` (+ `sha_core.rs`/`sha_gen.rs` vendored from Plonky3), `rcpt.rs`, `mrk.rs`, `sort.rs`, `acct.rs`, `node.rs`, `path.rs`, `fixed.rs`, `mod.rs` (shared helpers) |
| `source/src/witness.rs`, `trace.rs` | structured witness and trace generation; provider multiplicities from the AIR's own queries |
| `source/src/proof.rs` | prove, verify, proof framing, `public.bin`, AIR/config digest |
| `source/src/config.rs`, `security.rs`, `fingerprint.rs` | STARK configuration, security estimate, AIR fingerprint |
| `source/src/eval.rs` | concrete AIR evaluator (multiplicities, self-check, mutation tools) |
| `source/src/engine.rs`, `spec.rs`, `trie.rs`, `wire.rs` | native relation re-execution and formats (from `examples/reexec-witness`) |
| `source/src/bin/` | `prepare`, `prove`, `verify`; dev tools `npdev` (check, conform, shape, breakdown), `seccalc`, `mutproof`, `mutwit` |
| `source/vendor/` | vendored crates, **not in git**; create with `build-recipe/vendor.sh` |
| `formal/` | Lean project: spec, vacuous backend, abstract pipeline composition, status table; no certificate |
| `bench/` | `run-bench.py` and `results-2026-10-03/` (measurements, adversarial, probe, conformance, security) |

## Build

`build-recipe/vendor.sh` is the packager step and needs the network. It
vendors 86 crates, about 48 MB, and records `dependency-locks/`.
`build-recipe/build.sh` is the judge step. It runs offline with a fresh
`$HOME`, needs Rust 1.96.0, and takes about 45 s. It uses `--locked
--offline`, path remapping and stripped symbols, and pins the codegen
target to `x86-64-v3 + SHA-NI + AES-NI` (no `target-cpu=native`). In
testing, `x86-64-v4` (AVX-512) was no faster.

Two builds at different paths, each with its own fresh `$HOME` and under
`unshare -n`, produced bit-identical outputs:

```text
ee649c60409453c317a3ac634ebbea9bc65d57c50bca99397d0fc9edc9bd7e7c  out/prepare
aa40ee9ba9cc9c34694b8a7d5bafc17dd5ce63ea6900d2ce6ba3b438671aa9cf  out/prove
404da37049ba272b34fa3111edf193b823a2daef22d75212d6356c4e775e5017  out/verify
```

`arena pack` of the package is 41.9 MB (3199 files). Unlike the SP1 package,
it has no vendored `target/` directories, so the SDK packer's `target`
exclusion does not affect it.

## Reproduce

```sh
cd examples/stark-plonky3
bash build-recipe/vendor.sh && bash build-recipe/build.sh     # out/{prepare,prove,verify}
(cd source && cargo build --release --bins)                   # dev tools -> source/target/release/
T=source/target/release; F=../../oracle/fixtures/public
$T/npdev check $F/cases/*                  # prove (with native self-check) + verify + claim compare
$T/npdev conform $F                        # native conformance (also: oracle gen output dirs)
$T/mutwit --rows 4 $F/cases/s20261003-v5   # under-constraint probe
$T/mutproof --per-pattern 3 <dirs holding claim.bin + proof.bin>
$T/seccalc 12 8 8 8 6 6 12 8 12            # security estimate for given log2 table heights
python3 bench/run-bench.py --prover stark=out --params $F/params.bin <oracle gen --fixtures-layout dirs>
```

## Known gaps

* Nothing is formally proven: the AIR ↔ NearSpec refinement, completeness,
  STARK/FRI/LogUp/FS soundness and the Rust verifier binding are all open
  (EVIDENCE.md).
* The proven bound is below the profile even before formalization (above).
  The proof is 85% of the size cap.
* Prove time has a fixed floor of about 0.25 s. About 150 ms of it is
  Plonky3's symbolic AIR analysis in `ProverData` (lookup packing, quotient
  degree inference); `prove_batch` does further symbolic evaluation. Caching
  the lookup layout in `public_dir` or patching batch-stark would remove
  much of it. Verify repeats the same analysis (about 140 ms of its 230 ms).
* The challenge id is the signed formal challenge. The candidate is expected
  to be rejected at the formal gates.
