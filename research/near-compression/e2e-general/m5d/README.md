# E2E milestone M5d-T1: the FINAL and INIT templates for general chunks (lane G)

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §1.1 ("outputs and roots"), §3.2, §3.4, §5.0.1
(blocker 7, item 1(b)(ii)), §5.7 (status). Leaf-template spec for lane D:
[`LEAF-TEMPLATE-SPEC.md`](LEAF-TEMPLATE-SPEC.md). Date 2026-11-21. Labels: **[M]** measured here,
**[K]** kernel-checked Lean (std axioms), **[S]** stated / design only.

## G-2 (2026-11-21): whole-AIR Lean, the leaf joins, `B_out`, pinned shapes, class census

Log `docs/logs/e2e-laneG-g2-2026-11-21.md`. Plan §5.3.

### Item 1 — from `Holds` of the whole AIR [K]

The package now requires lane B's `StateM5a` (read-only: `Bus`, `ChipStub`, `Sha512If`).
**`Whole.finalAirS`** = `finalAir` + lane B's chip stub `chipStubOn B_IF384`: the AIR the prover
runs (`Holds finalAir` alone is unsatisfiable: `S384` receives on `IF384` and no Lean table sends
there). **`S384Chip.precheck_holds_final`**: a precheck-accepted trace (every bus but `IF384`
balanced, the native chip's sends a permutation of the `IF384` receives) extends, Lean tables
unchanged, to `Holds finalAirS` whose stub sends are exactly the chip's — so every theorem below
is about the deployed relation and the chip premise is lane B's `Sha512IfContract` on the chip's
own sends.

| module | result |
|---|---|
| `BusMem` | generic: `mem_busList` (bus list ↔ an occurrence), `recv_sent` / `sent_recv` under `Holds` |
| `Whole` | `onlyIn` / `occ_in` (who sends / receives a bus, `decide +kernel`), field ↔ natural helpers |
| `HbWhole` | **`hb_bytes`**: `HbBytes` (was a premise) from `Holds finalAirS` — `FIN` `HB` ← `STMT` (`h = 1 ⇒ act = 1`) → `SB` → `S384` data flag (`⇒ act = 1`, monotone flags) → `R8`/`S2`/`S5` → `RNG` (`v = Σ 2^i β_i`); `fin_row0_act`; **`final_template_sound_holds`** (FINAL with `HbBytes` discharged) |
| `RsRow` | (was `lean-wip`, over the heartbeat budget; now 0.8 s) `rs_parity_bit_holds`: parity bit = parity of the selected data bits, `q` bytes from `R8` |
| `RsByte` | **`rs_parity_byte_holds`**: an `RS` row's parity byte `i` = the spec's `parityPart` byte `⊕_j mulRow(M[d+i][j])[d_j]` (with `coeff_linear`, `mat_mem`) |
| `ShaWhole` | **`sha_msg`**: SHA-256 message identification — a received `SHA_DIGEST (id, L, dg)` whose `(id, i)` senders are functional is `sha256` of their bytes (`sha_digest_recv` from lane L5's closed contract; `|msg| ≤ 2^28`) |
| `MrkWalk` | **`walkRoot_eq`**: the `MRK` level walk (hash / carry / terminal / zero rows) is nearcore `merklize` (record level) |
| `S384Rec` | `sha384_of_blocks`: `sha384 m` = the first 48 bytes of `foldl compress IV384` over blocks concatenating to `pad m` |
| `S384Chip` | **`s384_comp`** (an active `S384` row is a chip compression, via lane B's `comp_sound`), `s384_step` / `s384_iv`, **`s384_chain`**: over a message, the compression input of row `r0 + n` is the fold of `compress` over the rows' blocks from IV384 |
| `Split` | item 3, below |
| `BOut` | item 2, below |
| `Cls.All` | item 4: `f1_eq` — the generated F1 class AIR is `finalAir` (`rfl`) |

**Still open for `Computed`** (named, in order of size): the functional-sender facts per SHA-256
consumer (`PART`/`RS` ids `PID0 + p`, `SHD` `SHM0/SHL0 + q`, `MRK` `MID0 + g`: disjoint id ranges
and row counters) — then `sha_msg` gives each digest; the `MRK` table's rows ⇒ `walkLevel` per
level (the `NODE` bus is functional on `(tree, level, index)`: one `TSTART` per tree, counters);
`BODY`/`SEG` ⇒ `encodeRcpts` and the shard routing; `S384`'s padding (the rows' blocks are `pad` of
the received bytes) and digest-byte extraction, which with `s384_chain` + `sha384_of_blocks` gives
SHA-384 of every `SD` message (then the accumulator openings, modulo `bdigest` collisions).

### Item 2 — `B_out`, pinned shapes, lane D's format [M]

* **Prover** (`prover/`): ported to lane B's B-T1 prover — the verifier's backend (frozen
  `pq-e2e-d9` `stark-backend-unified` + `plonky3-ext12`), `Sha384CpuEngine`, **lane D's base
  configuration** (list decoding m = 64, `k_first 2`, `domain_odd_factor 15`, LogUp message length 7,
  `zk = 0`) with **query grinding 24** (not 32) and the template's `(n_stack, log_blowup, w_stack)`;
  `prove … OUT` saves `STATE.proof`, `STATE.vk.json` (SavedVk), `statement.json`; **lane D's driver
  verifies them** (`nearproof-chunk-e2e fs-count VK PROOF 0`, `run.sh` runs it).
* **Pinned heights** (`templates/*.json`, `census.py`): every table — the SHA-256 table and the
  SHA-512 chip included (minimum-height options: `sha_cells_pinned`, `gen_main(comps, 1 << pin)`,
  zero rows) — padded to its class pin; FINAL classes nested by chip height `F1` (≤ 2^13, 120 / 133
  F1 cases), `F1-M`, `F1-L` (all 133); INIT classes `INIT-14 … INIT-18` by chip height (875 / 875 of a
  partial census). `run.sh` picks the smallest fitting template (exit 4 = overflow).
* **`B_out`** (`Final.lean` `Fin.boutInteractions`, `BOut.lean`): `FIN` sends `0x04 ‖ chunk_inner`
  and `0x05 ‖ encOutputsF1 o` (252 B, from the row's `FinIn` / root / header-length cells) through
  `S384`; public values 30..44 = `ctxD(.header H)` = `BOut.ctxHeaderD H`, 44..58 = the first
  component of `outD(.done o)` = `BOut.outDoneD o`. The dump emits **Lean's own** `ctxHeaderD`,
  `outDoneD`, `encOutputsF1` on the case and `tracegen.py` asserts the circuit's bytes equal them
  (T1: `ctxHeaderD = a1d33e43…92c7`, `outDoneD = ef7d1e4e…6c72`). The leaf assembles `h(B_out)` from
  these, `claimDigest` and the view's constants for `done` (§5 of the leaf spec).

| T1 | before (M5d-T1, seg-v1, natural) | G-2 (template, base config) |
|---|---|---|
| FINAL (before `B_out`) | 992,188 B | **480,428 B** at `F1` (27.6 s / 31 ms, 6.9 GB, 268.2-bit), fs-count OK |
| INIT (before the section-B walk) | 790,307 B | **346,723 B** at `INIT-14` (38.8 s / 16 ms, 6.2 GB), fs-count OK |
| FINAL with `B_out` / INIT with `BLK` | | G2_REPROVE |

**INIT decodes section B (G-2, coordinator request)** — `BLK` framing walk, slot bus, the main
slot's `prev_state_root` exposed (public values 28..44; bus `PSR` = 22 in the `.init` join); see
leaf spec §6 (the slot *selection* `(b2i, mainIdx)` = the checker's `walkSegment` is open: mutant
`psr_slot` is accepted by the AIR).

**Mutants:** the batteries could not run in this session — the shared `zkbuild.slice` (the `heavy`
wrapper's cgroup) sat at its 40 GB `memory.high` from other lanes' jobs, and every prover in it
(even the precheck) stalled in page reclaim; only `hdr_psr` completed before (rejected, FIN constraint
3 + native verifier). Re-run: `LEAN=0 ./run.sh CASE OUT mutants` and `TEMPLATE=init …` (the
battery runs the precheck first, the full prover only for mutants passing it). New mutants:
FINAL `bout_od`, `pub_hdr`, `pub_out`; INIT `lbshift`, `psr_slot` (expected: accepted — the open
selection), `pub_psr`.

### Item 3 — the FINAL / INIT leaves as joins [K] (`Split.lean`; lane E's M11i split was not on main)

* `finK_bind` (any driver, any gas cap): the checker's `finK … k = finK … pure >>= k` — `FINAL`'s
  first part splits at `t = (root, congestion, outgoing)` with no checker change; `FinReach I out t`
  (`∀ k, finK … k = k t`), `finReach_of`, and `fin_split` (every successful non-genesis `FINAL` step
  factors through such a `t`: the split is not vacuous).
* **FINAL**: lane B's `FinalBPart` (input digest opens to `fin I out`, `I.d2 = none`,
  `FinReach I out t`, the `FinIn` bus carries `fi` with `FinInOK fi I out t`) + lane G's
  `FinalGPart` (from the bus value: output digest opens to `done I.H o`, `tailNew … t = .ok o`,
  `headerOk I.H o`) ⇒ **`segSoundFinal_join`**: lane E's `SegSoundFinal`; `final_join_headerOk`
  also gives FinalOut on the opened `done`.
* **INIT**: `InitGPart` (input digest opens to `init cb wb` for the bytes on the `CLM` stream) +
  lane B's `InitBPart` (for those bytes, `CM.step (init cb wb) = .ok c`, output digest opens to `c`)
  ⇒ **`segSoundInit_join`**: `SegSoundInit`.
* What lane G's tables give toward `FinalGPart` today: `final_template_sound_holds` (`headerOk` of
  the decoded public header and `tailNew`'s `o`), modulo `ClassF1` / `Computed` and the `B_out`
  digest; `H = I.H` is the statement link (`cm_done_header`: the `done` header is the claim's own
  decoded `chunk_inner`, the window `FIN` reads from the statement whose digest is `ctx`).

### Item 4 — FINAL class census [M] (`shapes.py`, `logs/G2-shapes.{txt,jsonl}`)

7,477 `d3` cases (`d3c7`–`d3c10`, every 4th + the first 3,192), the Lean checker's FINAL per case:
**F1 is 3.7 %**; transactions are in **81 %**; `(d, t)` ∈ {(1, 3) 22 %, (2, 8) 25 %, (5, 16) 23 %,
(33, 100) 27 %}, not tied to the shard count (4 shards 37 %, 5 shards 32 %, 6 shards 31 %);
proposals 3.3 %, bandwidth requests 0.65 %, proposed split 0, header V5 and `|chain_id| = 14`
everywhere; 1 % dump timeouts (600 s). Without transactions / proposals / bandwidth requests every
`(NS, d, t)` combination together is ≈ 18 %; adding transactions reaches ≈ 96 %.
**`gen_class.py NS D T`** generates the class-`(NS, d, t)` FINAL AIR from `Final.lean` (the AIR is
parametric in exactly these; `FI_LEN = 246 + 8·NS`), `m5d-tool air-final-cls NS D T AIR NAMES`
exports it (9 classes generated), and `Cls.f1_eq` checks that the generated F1 is `finalAir`.
Next by frequency: transactions (the `SEG`/`BODY` path with the tx destination + tx accumulator +
`tx_root` merklize), then proposals, then bandwidth requests.

## What this is (M5d-T1)

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

**Targets in lane E's T1 template system** (`spec/lean/v3/NearSpecV3/E2E/Templates.lean`, main
`1461c97f6`): `SegSoundInit` (meaning `MInit`: the whole `CM` intake step `init cb wb → CM.step`)
and `SegSoundFinal` (meaning `MFinal`: a `CM` run from a finished engine configuration to `done`,
including `finK`). **What M5d-T1 covers of them:** INIT proves the init boundary's two
chunk-dependent digests (`claimDigest` bound to the canonical `S` of `StmtEnc`, and the
`ctxD (.raw cb wb)` commitment); the intake step itself (claim / witness decoding, trie
authentication) is lane B's INTAKE, so `SegSoundInit` needs INIT ∘ INTAKE in one leaf. FINAL proves
`tailNew` + `headerOk` from the post-`finK` point (`final_template_sound`); `finK` (main root check,
implicit transitions, outgoing reassignment) is lane B's FINAL root / M5c, so `SegSoundFinal` needs
them joined (leaf spec §4, option (a)). `TmplComplete` for the M5d part: the T1 proofs plus
`T1Check`.

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
| `STMT` | 1,007 | lane E's canonical statement `S = stmtPre ‖ u32 0 ‖ stmtPost` (plan §3.4.1, `StmtEnc`) → SHA-384 `claimDigest`; first 424 bytes → `FIN` |
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
| trace | 2,689,104 cells (SHA 2.23 M, chip 0.34 M, RS 55.8 k); 26 SHA-512 compressions | 1,616,828 cells (CLM 2^14, chip 2^14); 124 compressions |
| proof | **992,188 B** (whir 689,044, relations 274,548, gkr 25,544) | **790,307 B** (whir 681,396) |
| soundness (calculator) | 268.2 bits | 268.2 bits |
| prove / verify | 30.3 s / 83 ms (8 threads, 0.90 GB peak) | 56.1 s / 58 ms (0.81 GB) |
| outputs | outcome root `49be525c…`, outgoing root `647e6f58…`, encoded root `5a648fbd…`, length 990, state root `1db48e38…`, gas 1,577,739,758,301 — each = the Lean checker's (`dump.checks`, tracegen asserts) and = the header's | `claimDigest` = `bb5aad11…9f2f01` = lane E's `t1_claimDigest`; `ctxRoot` = `0e790a2c…f745f5fe` |

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
* `RsCoeff.coeff_linear` (kernel, 93 s): for every parity coefficient of the class matrix, every byte
  `x` and bit `k`, bit `k` of the spec's `gfMul c x` is the GF(2) sum the `RS` row constrains.
* `T1Check`: **non-vacuity on T1** — T1's actual row values satisfy `RowOK` (`decide +kernel`), the
  window is T1's public `chunk_inner`, `outputsOf` = the checker's outputs, `headerOk` holds.

Open (named premises, not yet theorems; `lean-wip/RsRow.lean` has the RS row's parity-bit lemma,
not yet within the heartbeat budget): `Computed` from `Holds` of the whole AIR (the `MRK` walk ⇒
`merkleRoot`, `RS` rows ⇒ `parityPart`, `BODY`/`SEG` ⇒ `encodeRcpts`, `SHD` ⇒ `outgoingRoot`, the
SHA-256 contract, the `S384` table ⇒ SHA-384 under lane B's `Sha512IfContract`); `HbBytes`;
`FinInOK` is the upstream segment's obligation (leaf spec §2).
