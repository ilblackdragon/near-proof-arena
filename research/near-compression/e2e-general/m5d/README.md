# E2E milestone M5d-T1: the FINAL and INIT templates for general chunks (lane G)

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §1.1 ("outputs and roots"), §3.2, §3.4, §5.0.1
(blocker 7, item 1(b)(ii)), §5.7 (status). Leaf-template spec for lane D:
[`LEAF-TEMPLATE-SPEC.md`](LEAF-TEMPLATE-SPEC.md). Date 2026-11-21. Labels: **[M]** measured here,
**[K]** kernel-checked Lean (std axioms), **[S]** stated / design only.

## What this is

* **FINAL** (class `F1`): every chunk-header output lane E's `headerOk` compares (13 comparisons)
  is computed in-circuit from the post-`finK` record `FinIn` and compared, byte by byte, with the
  chunk header inside the public statement, whose SHA-384 digest is the public `claimDigest`
  (recommendation 1(b)(ii): FinalOut is carried by the template, the wrap only checks `done`).
* **INIT**: the init boundary's chunk-dependent digests from the claim and witness bytes:
  `claimDigest` (the statement) and `ctxRoot` (the intake context `ctxD (.raw cb wb)`).

Both AIRs are `ZkFormal.Air` values in Lean (`lean/FinalM5d/{Final,Init}.lean`), exported by
`m5d-tool` and interpreted unchanged by the prover (`prover/`, a copy of lane B's M5a prover with
the table list read from the export; same backend, BabyBear Ext12, SHA-384 MMCS 42-B digests,
stacked WHIR, seg-v1 parameters, the native SHA-512 chip v4 on bus 103). Traces come from the Lean
checker's own run (`m5d-tool dump`: lane E's `CM.step` from `init claim witness` to `fin I out`,
then the checker's `finK` and `tailNew` verbatim).

## Commands

```
./build.sh                                     # lake build m5d-tool; cargo build (≤ 8 threads)
./run.sh CASE_DIR OUT_DIR prove                # FINAL: dump, export, tracegen, prove + verify
./run.sh CASE_DIR OUT_DIR mutants              # FINAL mutant battery (tracegen.py MUTANTS)
lean/.lake/build/bin/m5d-tool air-init A.json N.json  # INIT AIR; tracegen.py DUMP N.json OUT
python3 gen_t1data.py DUMP lean/FinalM5d/T1Data.lean  # the Lean non-vacuity data
( cd lean && lake build )                      # every lemma + FinalM5d/Audit.lean
```
`CASE_DIR` for T1: `/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3`.

## The FINAL AIR (class F1)

| table | rows (T1) | role |
|---|---|---|
| `SHA` | 2^12 (133 blocks) | `ZkFormal.Sha.Table` (contract `sha_digest_contract_closed`): every spec SHA-256 |
| `S384` | 2^5 (26 blocks) | **new**: SHA-384 of byte messages over the native compression chip — receives `(id, pos, byte)`, sends `(id, len, digest[48])`, FIPS padding in-circuit, bytes ↔ 21-bit limbs with split lookups |
| `RNG` | 256 | `R8 (v)`, `S2 (v, v mod 4, v/4)`, `S5 (v, v mod 32, v/32)` lookups |
| `STMT` | 1,007 | the statement stream `u32 |pre| ‖ pre ‖ post` → SHA-384 `claimDigest`; first 424 bytes → `FIN` |
| `FIN` | 1 | header window (fixed layout pins, the 13 comparisons), `FinIn` → `finInDigest`, roots, public values |
| `BODY` | 990 = d·L | the chunk body `u32 0 ‖ u32 n_R ‖ enc r_1 ‖ …` (+ zero padding to `d·L`): Reed–Solomon data cells, per-shard and accumulator-chain message bytes |
| `SEG` | 7 | segments: the two count prefixes, one per outgoing receipt (shard one-hot, length, chain step `acc_{i+1} = bdigest(acc_i ‖ u64 shard ‖ u32 ℓ ‖ enc r)`), padding |
| `RS` | L = 198 | Reed–Solomon parity, **GF(2)-linear**: data bits `x`, per parity bit `Σ A·x = r + 2q` with `r` a bit and `q` an `R8` lookup; part bytes → SHA-256 |
| `PART` | t = 16 | part leaves `sha256(u32 L ‖ part)` |
| `SHD` | 6 | shard leaves `sha256(sha256(u64 s ‖ u32 n_s ‖ receipts routed to s))` (`merklizeBorsh`) |
| `OUTL` | 2 | outcome leaves: accumulator chain `bdigest(acc ‖ leaf)` and Merkle leaves |
| `MRK` | 25 | nearcore `merklize` as a level walk (odd node carried up, `n ∈ {0,1}` terminal rows) for the outcome, shard and part trees |

Public values: `claimDigest` (14 limbs of 3 bytes), `finInDigest` (14), `n` (body length), `L`.
Class `F1` pins: header V5, no proposals / bandwidth requests / proposed split / transactions,
6 shards with `u16` ids, `|chain_id| = 14`, Reed–Solomon `(d, t) = (5, 16)`.

## Results on T1 [M]

| | FINAL | INIT |
|---|---|---|
| trace | 2,689,104 cells (SHA 2.23 M, chip 0.34 M, RS 55.8 k); 26 SHA-512 compressions | see below |
| proof | **989,626 B** (whir 686,482, relations 274,548, gkr 25,544) | see below |
| soundness (calculator) | 268.2 bits | |
| prove / verify | 35.0 s / 102 ms (8 threads, 0.93 GB peak) | |
| outputs | outcome root `49be525c…`, outgoing root `647e6f58…`, encoded root `5a648fbd…`, length 990, state root `1db48e38…`, gas 1,577,739,758,301 — each = the Lean checker's (`dump.checks`, tracegen asserts) and = the header's | |

The dump's self-checks: every output recomputed the way the AIR does it (merklize of the outcome
leaves, per-shard `u64 s ‖ encodeRcpts` double hash, `buildMatrix` parity, parts root) equals the
checker's `tailNew` output, and `headerOk I.H o` holds.

**FINAL mutants: 32/32 rejected** (`logs/T1-final-mutants.txt`):
* statement (one byte of each compared header field, the statement re-hashed honestly so only the
  AIR can catch it): `hdr_psr, hdr_por, hdr_emr, hdr_el, hdr_gu, hdr_gl, hdr_bb, hdr_orr, hdr_txr,
  hdr_props, hdr_cong, hdr_bw, hdr_split` — all 13 comparisons;
* boundary (`FinIn`, re-hashed honestly): `fin_root, fin_cong, fin_gas, fin_bal, fin_gl`;
* data (recomputed honestly downstream, so the computed root differs from the header's):
  `leaf, outcome_drop, rcpt_byte, rcpt_shard, rcpt_drop, rcpt_swap`;
* row tampers: `body_byte, rs_par, mrk_node, stmt_byte, fin_ro, s384_pad`;
* public values: `pub_claim, pub_n`.

## Reed–Solomon in-circuit cost (measured on T1, projected) [M][E]

Per body byte, cells (unpadded): `BODY` 17; `RS` `(8d + 16(t−d) + 2)/d` = 43.6 at (5, 16), 40.5 at
mainnet-like (33, 100); **part hashing `(t/d)·144.5`** (a SHA-256 block is 17 rows × 544 = 9,248
cells per 64 B) = 462 at (5, 16), 438 at (33, 100); receipts also pay their shard-message SHA-256
(144.5) and the accumulator chain's SHA-384 (S384 3.5 + chip 83). On T1 the part messages are
64 of 133 SHA-256 blocks (48 %); the parity arithmetic itself is 55.8 k cells (2 % of the trace).
**The cost of `encoded_merkle_root` is the spec's SHA-256 over `t/d ≈ 3×` the body, not the GF
arithmetic**: ≈ 500 cells per body byte, i.e. ≈ 0.5 G cells for a 1 MB body [E]. Levers: none on
the hash (spec); the part tree's `t − 1` nodes are fixed per chunk (≈ 2·t blocks).

## Lean [K] (`lean/FinalM5d/`, std axioms only — `Audit.lean`)

* `Decode.decode_F1`: the class-F1 byte layout `encF1` decodes (the spec's `decodeChunkInner`) to
  `hdrF1` with the slices as fields.
* `HeaderLink.row_headerOk`: `RowOK hb fi ro rs rsh n` (the `FIN` row's relations, as naturals) ⇒
  `decodeChunkInner (win hb) = .ok (hdrOf hb)` ∧ **`headerOk (hdrOf hb) (outputsOf fi ro rs rsh n)`**.
* `FinRow.rowOK_of_constraints` / `fin_headerOk`: on any row of any trace where the exported
  `Fin.table`'s constraints vanish over BabyBear with `act = 1` and byte-valued statement cells
  (`HbBytes`, a named premise: `S384`'s lookups range-check them), `RowOK` holds of the cells — so
  the row gives `headerOk`.
* `Tail.tailNew_outputsOf` / **`final_template_sound`**: with `FinInOK` (the `FinIn` cells are the
  projection of the post-`finK` point `(I, out, t)`), `ClassF1` and `Computed` (the received roots
  are the spec's outcome root, outgoing root and `encodedMerkleRoot` of the body), the checker's own
  `tailNew afDriver I out t = .ok o` and `headerOk H o` for the decoded public header `H`.
* `T1Check`: **non-vacuity on T1** — T1's actual row values satisfy `RowOK` (`decide +kernel`), the
  window is T1's public `chunk_inner`, `outputsOf` = the checker's outputs, `headerOk` holds.

Open (named premises, not yet theorems): `Computed` from `Holds` of the whole AIR (the `MRK` walk ⇒
`merkleRoot`, `RS` rows ⇒ `parityPart`, `BODY`/`SEG` ⇒ `encodeRcpts`, `SHD` ⇒ `outgoingRoot`, the
SHA-256 contract, the `S384` table ⇒ SHA-384 under lane B's `Sha512IfContract`); `HbBytes`;
`FinInOK` is the upstream segment's obligation (leaf spec §2).
