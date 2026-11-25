# E2E lane F: the runtime rows of T1's FunctionCall receipt (M5-T1), the `rt` leaves (F-2), the relative store-canonical form (F-3)

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §3.3 (Wasm ↔ state join), §4.2 (M5), §5.2 (status).
Date 2026-11-21 (F-3: 2026-11-25). Labels: **[M]** measured here, **[K]** kernel-checked Lean (std axioms, no `sorry`),
**[S]** design / stated only.

Target T1 = `d3c8/d3/02-h10196-s3`. Its one incoming receipt (`78c006d5…`, `s2a04 → s5k210.s2a00`,
FunctionCall `run("again")`, prepaid 54 Tgas, deposit 10⁻³ NEAR, gas price 1 Gwei, chunk gas price 0)
is what these rows execute. Its transaction and the two buffered-receipt forwards are other templates
(STATE / M5c).

## What is built

| piece | file | what it is |
|---|---|---|
| Lean run recorder | `lean/M5T1/Dump.lean`, `m5t1-tool dump` | the checker's own `intakeK` + `estep` (lane E's `CM`), every incoming receipt through the oracle form `pwO` (`CutW.lean`, `pwO_std`) with the checker's VM plus a recorder: receipt, RS before/after, VM query (`CallCtx`) and answer (`Run`), outcome, new receipts. `estepAgrees: true` on T1 |
| AIR (single source of truth) | `lean/M5T1/{Ids,Schema,Msg,Rx,Air}.lean`, `m5t1-tool air` | tables `SHA` (unchanged ZkFormal SHA-256), `RNG`, `SCHT`, `MSG`, `DG`, `RX` + two cached tapes |
| trace generator | `tracegen.py` | builds every table from the Lean run and **asserts** each derived value against it |
| prover | `prover/` | lane B's harness (interprets the exported AIR unchanged) without the SHA-512 chip, on the main stack |
| run script | `run.sh CASE OUT [check\|prove\|mutants]` | dump → AIR → trace → prove / mutant battery |

**`MSG`: a schema-driven Borsh engine** (one row per byte). A message type is a list of segments:
a constant byte, a field the bytes *define* (parse; offered on `FB (128·qf + fid, k, b)`), a field
*used* (copied from `FB`), a u32 length prefix parsed (`FLEN` offered, next segment's length set,
an empty field skipped) or emitted (`FLEN` received). Every row receives its schema entry from the
constant table `SCHT`. The messages of T1's receipt:

| type | spec encoder | out |
|---|---|---|
| `RL` | `encodeRcpts I.receipts` (single-FunctionCall V1 action receipts) | SHA-256 = `w.appliedReceiptsHash` (statement) |
| `KEYR`/`APRE` | `kAccount recv`, `Acct.encode` (V1) | read: lane B's read design (`SRQ` + key on `HB`, `SRS` + value on `HBR`) |
| `KEYW`/`APOST` | the new account | **lane B's `SREQ` + `HB`** (the shape its STATE rows consume) |
| `AH`, `SEED` | `actionHash rid h 0`, `sha256 (ah ‖ randomValue)` | VM context `action_hash`, `random_seed` |
| `RID` | `receiptIdFrom rid h 0` | the refund receipt id |
| `RREF` | `Rcpt.encode` of `D2.refunds`' gas-refund receipt | hash → `OUTR` |
| `LOGi`, `PART`, `LEAFn` | log bytes, `OutD1.partialEncode`, the preimage of `OutD1.leaf` | leaf → `OUTC` |

`tracegen.py` parses the spec's own byte strings with the schema, so the schemas are checked against
the Lean run's `encode` / `partialEncode` / `leaf` / refund `encode` on T1 (all equal).

**`RX`: one row per receipt** (1,364 columns, 2,537 constraints, 1,501 interactions, degree 4). Every
number is little-endian bytes (`RNG`-checked); every `u64`/`u128` operation is a carry chain with the
spec's overflow checks as a zero top carry. It computes: `actExec` of the FunctionCall
(`780 G + 2,235,934·(|m|+|a|)`), the merge (`gas_burnt = nar + ex + burnt`, used, compute,
`burnt ≤ used`), the deposit overflow check, V1 account / local contract, the storage stake of the
account the call leaves, `burn = min(purchase, gas price)`, `pred ≠ system`, `D2.refunds`
(`purchase·(prepaid + exec − used) + (purchase − burn)·burnt`, `> 0`), tokens burnt `burn·burnt`, the
receiver reward `burn·⌊3·gasFC/10⌋` with the new balance and the `tx_burnt` share, the receipt state's
totals (gas, compute, `tx_burnt`, subsidized, wasm gas, outcome / outgoing counts), `compute <
gas_limit` (else delayed), `gas ≠ 0`, the method / args size limits. It demands its messages
(`MBEG`/`MLEN`), sends the call request `VMCALL (qf, ts)` and reads the answer `VMRES` + the VM's
fields on `FB`, sends `OUTC (qf, leaf)` and `OUTR (qf, refund hash)`. Public values: the env (gas
price, height, timestamp, epoch height, random value, gas limit), the segment, the clock in/out and the
receipt state's totals in / out (plan §3.2 gas-and-balance group).

**Interfaces (plan §3.3).** The Wasm call's context is the receipt family's `FB` fields (method, args,
accounts, signer key, prepaid gas, deposit, balance, locked, storage usage, code hash, action hash,
random seed, height, timestamp, epoch height): lane A's context-getter HOST rows look them up there.
The answer is `VMRES (qf, tsEnd, ok, nLogs, nActions, retIdx)` + `FB` fields 70–75 (burnt, used,
compute, balance, storage usage, subsidized), the log fields 56+i and the return field 61. The
account write is lane B's `SREQ`/`HB` unchanged; the account read follows lane B's §M5b read design.
On T1 the counterparts are the public stand-in tape `XTAPE` (exactly as lane B's `HTAPE`): it carries
the Lean run's `CallCtx` values (so the request is checked equal to the Lean `VmQ`), its `Run` answer,
and lane B's side of the account read / write (the Lean run's account bytes before / after).

## Results on T1 [M]

| | |
|---|---|
| proof (main stack, 268.2-bit) | **1,158,991 B** (`gkr` 20,408, `relations` 355,100, `whir` 780,168) |
| prove / verify / peak RSS (8 threads) | 5.7 s / 105 ms / 107 MB |
| committed cells | 369 k (SHA 2⁹ rows, MSG 832 rows in 2¹⁰, RX 1 row in 2², SCHT 1 row) |
| outputs = the Lean run's | outcome leaf `e63a8497…`, gas burnt 1,009,188,008,301, tokens burnt 0, status `SuccessValue("again")`, receipt id `331e3c0b…`, refund 54,888,077,387,472,000,000,000 yocto, refund receipt hash `aa203713…`, receiver balance 36.001 NEAR / usage 573, totals out gas 1,577,739,758,301, compute 1,732,463,022,301, wasm gas 121,110,620,829 (`logs/T1-expected.json`) |
| mutants | **8/8 rejected** (`logs/T1-mutants.txt`): `gasburnt` (outcome claims +1 gas), `refund` (refund receipt +1 Gwei·gas), `status` (empty `SuccessValue`), `rcptid` (refund receipt id flipped in outcome and receipt), `statement` (claimed chunk gas used +1: native verifier), `acctpost` (account write +1 yocto), `logbyte` (hashed log ≠ logged bytes), `vmburnt` (row charges 1 gas less than the VM answered) |

The 355 kB `relations` term is the `RX` row's 2.5 k constraints / 1.5 k interactions and `SCHT`'s
3,255 columns of opening values; the obvious levers are splitting `RX` into narrower multi-row tables
and a row-per-entry schema table.

## Lean link [K] (`lake build M5T1 m5t1-tool` green, 331 jobs; `logs/axioms.txt`)

* **Field → integers** (`Ize.lean`): `ize_mod`, `ize_eq_zero` (a vanishing constraint below `p` in
  absolute value is an integer equation); `chain_val` (carry chains); `Gadget.lean`: `lin_val`
  (the `Rx.lin` gadget is exact), `ize_mulT`, `conv_le`, `val_pad`; schoolbook products
  `conv_16_8/8_8/16_6/3_3` (`grind`).
* **`RxField.rx_rel_of_row`**: on *any* trace, a row where every `Rx.table` constraint vanishes, with
  `act = 1` and the `RNG` facts (bytes `< 256`, `r10 + 246 < 256`), has decoded values in **`RxRel`**
  (`RxSem.lean`: ~60 equations and bounds — every relation above). Bits come from the table's own
  booleanity constraints.
* **`SpecLink`** (sub-agent, reviewed): under `RxRel`, the spec's own functions compute the row's
  values: `consts` (every constant = `Fees.*`/`Lim.*`/`Params.*`), `actExec_fc`, `prepaidExec_fc`,
  `totalPrepaidGas_fc`, `totalDeposit_fc`, **`refunds_fc`** (`D2.refunds r a res gp burn false =
  .ok ([refundRcpt a.signer a.signerPk rf], 0)`), `stake_fc` (`storageStakeOk … = some true`),
  `merge_fc` (the merge's `add64`s and both asserts), `burnt_fc` (step 8 of `applyActionReceipt`),
  `totals_fc` (`processWithTotals` / `rs.txBurnt` / `rs.subsidized` / `rs.wasmGas`),
  `validActs_fc`.
* **Non-vacuity** (`T1.lean`): `t1_rel : RxRel t1Vals` (T1's decoded proved row, kernel `decide`),
  `t1_spec`.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`.

## F-2 (2026-11-21): `SegSoundRt` pieces, the `rt` leaves, size

Lane E's `rt` template (`spec/lean/v3/NearSpecV3/E2E/Templates.lean`, `MRt`) has T1 instances
**enter** (`eng I c → call I c [] q .pre`) and **resume** (`call I c [] q (.fin r) → eng I c'`,
the receipt step with the VM answered from the tape). Lane I's driver plan
(`/data/illia/nearproof-deps/e2e-t1/run4/plan.json`) cuts them as segments 2 and 5.

### Lean [K] (`lake build M5T1 m5t1-tool`: 398 jobs, green; `logs/axioms.txt`: std axioms only, no `sorry`)

| file | what is proved |
|---|---|
| `Obl.lean` | **Finding F2-1**: `TmplSound` is *absolute* — `tmplSound_image`: every input digest an AIR accepts must be in the image of `bndOf V.bnd` (or `Bad`), which no segment's rows can establish. `TmplSoundFrom` (relative: *given* `bndOf x = d`, the output opens to a meaning successor of `x`), `from_of_sound` (absolute ⇒ relative modulo collision) and **`e2e_sound_t1_from`** (lane E's `e2e_sound_t1` from the five relative premises, by induction from `B_0`, same conclusion). Spec untouched. |
| `Bus.lean` | `recv_sender` (a receive is matched by a send: `Holds`' exact balance); RNG row `r` holds `r` (`rng_row`), `rng_recv`; **`rx_hyps_of_holds` / `rx_rel_of_holds`**: every active `RX` row of a `Holds (fullAir tape xtape)` trace is in `RxRel` — the byte-range premise of M5-T1's `rx_rel_of_row` is discharged. No native-chip bus: `fullAir` is the Lean tables plus the two explicit tapes, so `Holds` is the circuit's own predicate (premise only: the tapes send nothing on `RNG`). |
| `Walk.lean` | the semantic interface: a message = a `Walk` over the schema (visits, `VisitOK`, `EndOK`/`ContOK`, `nextSeg`/`nextPl`/`newRAt`). |
| `MsgSpec.lean` (sub-agent) | **walk → encoder, for every walk**: `rl_spec` (`encodeRcpts` of single-FunctionCall V1 receipts, `FcShape`, per-receipt families), `key_spec` (`kAccount`), `acct_spec` (`Acct.encode`), `ah_spec`/`seed_spec`/`rid_spec` (`actionHash`, seed, `receiptIdFrom` preimages), `rref_spec` (`Rcpt.encode` of the refund receipt), `log_spec`, `part_spec` (`OutD1.partialEncode`, incl. the empty return), `leaf_spec`/`leaf_link` (`OutD1.leaf`); non-vacuity examples. No layout mismatch. Caveats (what the walk alone does not pin): RL count vs receipt number, RREF's two signer visits equal only via `FB`, RREF id = the RID digest (refund is receipt 0), LEAFn's count field from `RX`, APRE `u128::MAX` sentinel. |
| `MsgRow*.lean` (sub-agent) | **rows → walk**: `sch_row` (every `MSG` row's descriptor is a schema entry, = `segAt mt s`), `span_of` (every active row lies in a message span), **`msg_walk`** (a span `r0..r1` is `IsMsg mt mf (its b bytes) vs`), `span_start_unique`; **`dg_digest`** (an active `DG` row's 32 digest bytes are `sha256` of its message's bytes, via ZkFormal's closed SHA-256 table soundness), `mIdBound_of` (message ids `< 2^24` from the `RX`–`MBEG` balance) and `dg_digest'`. Premises: `SchtFixed` (the preprocessed schema columns, pinned by the vk), tapes send nothing on `SCH`/`RNG`/`SHA_BYTES`/`SHA_DIGEST`/`MLEN`/`MBEG`. |
| `BndLay.lean`, `Ent.lean` | the `rt` leaves' public values: **the boundary pair as `BndRec.encode` bytes** (F-2: `engF` 408 B / `callF` 784 B; F-3: 450 / 834 B, one byte per public value), `enterCons`, `resumeCons`. |
| `SegRt.lean` | (F-2 version; superseded in F-3 by `SegRt` per-rule semantics + `EnterC.enter_relC`) enter edge: `carried_eq`, `const_eq` (field-by-field semantics of `ENT` on any satisfying trace), **`segSoundRt_enter_from`**: the relative obligation for enter under the named view contract `EnterView V` (position non-final inside `stRoot` — lane B, review-D7 I3; the `.pre` Wasm record — lane A/PREP; `V.clear`'s `t`/`rPrepaid`), else a 42-B SHA-384 collision. |

**Not yet proved (in order).** (1) Resume: compose `rx_rel_of_holds` + `SpecLink` + `msg_walk`/`MsgSpec` + `dg_digest` into `estepO (strictO (K ++ [(q, r)])) I.prog c = .ok c'` (the monadic `applyActionReceiptW` step: overlay reads/writes, recorder, `emitReceipts` forward/buffer, the action loop's other branches) and the resume view contract (stRoot / outcome accumulator / `vmAcc` updates, which the template carries today); FB single-definer uniqueness (needed to read field values as functions). (2) `TmplComplete .rt` on T1: measured only (both leaves prove at the driver's records and digests [M]); no Lean statement for a concrete `ViewImpl` (none exists yet: lane I's driver has placeholder components).

### The `rt` leaves on T1 [M] (`run.sh CASE OUT leaves`; `logs/F2-leaves.txt`)

Lane D's base configuration (lane B's B-T1 `base_params`: first-order certificates, list decoding
m = 64, query grinding 24 bits, `domain_odd_factor` 15, tight heights floored to the full height),
pinned per template (`templates/rt-enter.json`, `templates/rt-resume-T1.json`); proof + vk +
`statement.json` saved (`RT.proof`, `RT.vk.json` — the stack's `SavedVk` envelope); the boundary
digests recomputed from the public values **equal lane I's plan** (`rtbnd.py` also asserts it).

| leaf | params | heights | proof | prove / verify / RSS (8 thr, host load ~37) | `d_in` → `d_out` |
|---|---|---|---|---|---|
| enter (`ENT`, 410 constraints on 1,192 public values) | ns 10, lb 7, w 8 | `ENT 2` | **87,001 B**, 268.8-bit | 8.9 s / 1.6 ms / 1.2 GB | `a2e7b254…` → `c667b45b…` |
| resume (M5-T1 rows + `resumeCons`, 1,439 public values) | ns 14, lb 5, w 10 | `SHA 9, RNG 8, SCHT 8, MSG 10, DG 3, RX 2, TAPE 6, XTAPE 9` | **431,245 B**, 268.3-bit (`relations` 136,608, `whir` 272,638, `gkr` 13,832) | 23.7 s / 32 ms / 9.9 GB | `6048b455…` → `aecc4056…` |

At lb 7 the resume leaf is 528,459 B but needs 32.7 GB (throttled at the 40 GB cap); lb 5 is pinned.
**Mutants** (`logs/F2-mutants.txt`): resume 11/11 rejected (M5-T1's 8 + `bndgas` output boundary
gas + 1, `bndprepaid` call boundary prepaid + 1, `bndburnt` in-flight burnt − 1), enter 4/4
(`phase`, `gas`, `stroot`, `clock`).

**What the leaves carry (interface items).** `resumeCons` ties `gasUsed`/`gasBurnt`/`compute`/
`balanceBurnt` in/out to `RX`'s receipt-state totals, `rPrepaid` to the receipt's prepaid gas,
`rBurnt`/`rUsed` out to the VM's answer; both edges carry `claimDigest`, indices, `stRoot`,
`ctxRoot`, the accumulators and `vmAcc` (placeholders / partial in lane I's driver). Owed by others:
the outcome accumulator update `chainD(leaf)` (lane G's `outcomeAcc` definition; the leaf is on
`OUTC`), `stRoot` after the account write (lane B), `vmAcc` (lane A/E), the `.pre` and `fin r` Wasm
records (lane A, PREP), the env values (gas price, height, timestamp, epoch height, random value,
gas limit) from `ctxRoot` (lane G's INTAKE; public values today), `XTAPE` (M6), the receipt from
`ctxRoot` instead of re-parsing the whole receipt list per resume.

### Size (item 3)

* **`SCHT` → one row per schema entry, entries preprocessed** (in the vk; `Msg.lean`, prover
  `air.rs` `prep`): 3,255 → 44 columns; the resume leaf's `relations` term 290,732 → 136,608 B at
  equal parameters' structure (−154 kB; 528 KB → 431 KB together with lb 5).
* **Not done: splitting `RX`** (1,368 columns, 3,010 constraints, 1,505 interactions on one row):
  the remaining `relations` mass. Plan: one row per 16-byte limb operation (a `u128` ALU table fed
  by a per-receipt op tape), `RX` keeping only the flags and the bus wiring.

### Coverage beyond T1 (item 4, scoped)

T2's shapes (`d3c9/d3/00-h10018-s0` and the plan's T2 list) need, per action: `CreateAccount`
(no contract: `existenceOk` without an account, `created` in `D2.refunds`, `storageStake` of the
new account), `DeployContract` (code hash = SHA-256 of the code, the deploy tracker / committed
code, the code bytes on the state side), `Transfer` (deposit only, no VM call: a STATE-template
receipt), promise-creating calls (`VMRES.nActions > 0`: `manager`/`distribute`, new receipts
through `finishActs`, their ids, `ret = receiptIdx`) and multi-action receipts (the action loop's
merge per action, `isLast` receivers). The schema engine is general (new message types are
schema entries + `MsgSpec` lemmas); `RX` needs per-action rows (the split above) before more
action kinds fit.

## F-3 (2026-11-25): lane F's templates in lane E's relative, store-canonical form (M11i)

Lane E's M11i (plan §3.5) made the per-template obligation **relative and store-canonical**
(`StoreBlind.TmplRelC`, `TreeM8C.TmplSoundRel8C`: every canonical opening of the input digest
steps to a canonical opening of the output digest), changed the record (`WasmBnd.gasLeft`; the
engine-state outgoing accumulator is the singleton `[chainD enc rs]`, G-3 item 2) and fixed S2
(`preCodeRoot q = SHA-256(q.code) ‖ 0^10`, the `.pre` record's `codeRoot`, written by the enter
leaf). Log: [`docs/logs/e2e-f3-runtime-2026-11-25.md`](../../../../docs/logs/e2e-f3-runtime-2026-11-25.md).

### The leaves on the M11i record [M] (`logs/F3-leaves.txt`, `logs/F3-mutants.txt`)

* **Layout** (`BndLay`): `engF` 450 B (`outRcptN`, `outRcpt0`: the singleton list), `callF` 834 B
  (`gasLeft` after `fuel`). The pairs come from lane I's run4 plan in the M11i shape (`rtbnd.py`:
  singleton accumulator with the plan's placeholder digest, `gasLeft = 0`; every other field is
  the plan's), so the digests differ from the plan's (lane I's driver is pre-M11i).
* **Enter AIR** (`BndLay.outRule`, `enterCons`; 762 constraints, was 410): per output field a rule —
  copy, constant, constant digest, free, padded. New: the **`.pre` Wasm record** (lane A's `fbBnd`:
  `pc`, `sp`, `stackRem`, `fuel`, `gasLeft`, `memPages` = 0; `framesDigest`, `memRoot`,
  `globalsDigest`, `registersDigest`, `promisesDigest`, `funcRoot` = `bdigest []`) and **S2**:
  `codeRoot = h ‖ 0^10` with `h` the receiver's code hash (the 32 bytes the receipt rows read from
  the account record, `APRE` bytes 32..64; T1: `8152bed2…36bf9` = SHA-256 of the 345-B `d3tiny`).
  The plan put the Wasm *entry* record at the enter cut; under M11i PREP (`.pre → .ent`) is a
  `wasm` leaf, so enter ends at `.pre`.
* **Proofs** (lane D's base configuration, pinned templates unchanged, 8 threads):

| leaf | proof | bits | prove / verify / RSS | `d_in` → `d_out` | mutants |
|---|---|---|---|---|---|
| enter (1,284 public values) | **87,739 B** | 268.8 | 2.4 s / 1.0 ms / 1.2 GB | `b850f1e5…` → `c320b92b…` | **10/10** (F-2's 4 + `coderoot` pad byte, `prefuel`, `gasleft`, `framesdig`, `outrcpt`, `inphase`) |
| resume (1,531 public values) | **430,143 B** | 268.3 | 17.0 s / 20 ms / 9.9 GB | `7fccc1fa…` → `6e1fe8a5…` | **11/11** (M5-T1's 8 + F-2's 3) |

  Both imported by **lane D's `m8-import`** (verifies natively; `M8_TEMPLATE_PROVED`) into the M8
  leaf format at `/data/illia/nearproof-deps/e2e-m5t1/f3/tmpl/{rt-enter,rt-resume}/`
  (`TMPL.proof`, `TMPL.vk.json`, `INFO.json`); `results/f3/` holds `INFO.json`, `statement.json`,
  `SHA256SUMS`.

### Lean [K] (`lake build M5T1 m5t1-tool`; std axioms only, no `sorry`)

| file | what is proved |
|---|---|
| `SegRt.lean` (rewritten) | the enter constraints' semantics per output rule on any satisfying trace: `copy_sem`, `num_sem`, `dig_sem`, `pad_sem` (S2's zero padding), `in_sem` (input phase 1, `inCall 0`, no Wasm part). F-2's `segSoundRt_enter_from` (under the contract `EnterView`) is superseded and removed. |
| `EnterC.lean` | the record ↔ public-value bridge: `enc_eng` / `enc_call` (`BndRec.encode` = the fields in `BndLay` order), `bytesOf_lay`, `flat_inj`, `len_eng`/`len_call`, `rules` (the 37 fields' rules, by evaluation), `bnd_enter` (the view of `call I c [] q .pre` = the engine record relabelled + the `.pre` part); **`enter_relC`** (`TmplRelC` shape: every canonical opening `x` of the input digest steps by `MRt.enter` to the canonical opening `call I c [] (setArgs (sf I) q) .pre` of the output digest, or a 42-B SHA-384 collision), `enter_open`, `enter_core`, **`enter_relC8`** (the M8 `TmplSoundRel8C` shape at leaf statements `(phase, digest)`), `enter_notInit` (its part of `NotInitIn`). |
| `T1Enter.lean` | **non-vacuity on T1's real enter leaf**: `t1_ent_holds` (`Holds Ent.entAir` on the leaf's own 1,284 public values; kernel evaluation in 8 chunks, 3 GB), `t1_checks` (incl. **`SHA-256` of T1's 345-B contract in the kernel** = the `codeRoot` bytes), `t1_rtView` (a view `V1` meeting every `RtView` law), **`t1_enter_nonvac`** (all premises of `enter_relC` hold together, `bndOf V1.bnd (eng I c)` = the leaf's input digest) and **`t1_enter_opens`** (the conclusion's canonical opening exists) — for every non-final `eng I c` and every query with T1's code. |
| `SplitC.lean` | **`split_sound_relC`** (`EngHalfRC` ∧ `StHalf` ∧ `SplitGlue` ⇒ `TmplSoundRel8C`: lane E's `split_sound` in the relative canonical form), **`glue_of`** (`SplitGlue` from lane F's side `ReqsFaithful` and lane B's side `ApplyFaithful`), **`rt_relC8`** (`TmplSoundRel8C … .rt` for the `rt` kind = enter ∨ the other `rt` programs, from `enter_relC8` and the named `RtOthers`). |

**What `enter_relC` rests on** (`EnterC.RtView`, `EnterC.EntChecks`), by owner:

| premise | owner | status |
|---|---|---|
| `RtView.preW`: `wasmD (some (q, .pre)) = preRec (vmc q) q` (S2 `.pre` record) | A | lane A's `fbBnd` still has `codeRoot = bdigest []`; the change is the plan's S2 instruction |
| `EntChecks.vm`: the output's `vmCtxDigest` is `vmc q` (lane A's remainder digest of `(q, .pre)`) | A | named: a copying leaf cannot exhibit a preimage of `encRest`; closes when the leaf (or PREP) parses the remainder |
| `RtView.pos`, `EntChecks.pos`: the input's `stRoot` shows a non-final position | B | named (`StCommit.rest` opening, review-D7 I3) |
| `RtView.clearEnter` (clear fields of `call I c [] q .pre` = those of `eng I c` with `t := 0`, `rPrepaid := pre q`), `outOne`, `noWasm`, `wf`, `blind` | E (view shape) | met by `V1`; `clearE` meets `clearEnter` with `pre = 0`; `blind` needs lane A's store-blind `wasmD` (S1) |
| `EntChecks.prepaid` (`rPrepaid = pre q`), `EntChecks.code` (`h = SHA-256(q.code)`) | **F** | **open**: the enter leaf has no receipt rows; closes by joining enter with the receipt family's `MSG`/`RX` rows that read `RX.gas` and the `APRE` code hash (and, for `h = SHA-256(code)`, lane B's account read + PREP's SHA-256 of the code) |

**Resume and STATE (not discharged).**
* **Finding F3-1.** The resume AIR *carries* `stRoot`, `outcomeAcc`, `outRcptAcc` and `vmAcc`, so
  for any view whose state commitment sees the receipt step (the position advances: `stOfK κ I c ≠
  stOfK κ I c'`) the output digest does not open — the relative obligation is unprovable for the
  current resume AIR, not just unproved. Needed: the split with lane B (`stRoot` from the state
  half, `SplitC.split_sound_relC`), the accumulator appends in-circuit (`outDE (.eng a)`: one
  SHA-384 per outcome / refund receipt, `Ser.enc` items — the resume prover has no SHA-512 chip
  today), `vmAcc' = bdigest []` (T1: `K = []`), and the `estepO (strictO (K ++ [(q, r)]))`
  composition (F-2 open item 1). Stated as `SplitC.RtOthers` (named premise of `rt_relC8`).
* **Finding F3-2 (clear fields).** Lane E's `viewE` uses `clearE` (all counters `0`; the gas totals
  live in `stRoot`'s receipt state), while the resume leaf ties the boundary's `gasUsed` /
  `gasBurnt` / `compute` / `balanceBurnt` / `rPrepaid` / `rBurnt` / `rUsed` to `RX`'s totals and lane
  I's driver fills them with the run's counters. Under `clearE` an honest resume leaf cannot
  satisfy its own boundary constraints (T1's totals are not 0). Decision for lane E / owner: the
  clear fields carry the counters (driver view), or resume takes the totals from the `stRoot`
  opening (lane B's `rest`). Enter is neutral (`clearEnter` is parametric in `pre`). Not a change
  of `S`, `claimDigest` or the checker.
* **STATE.** Lane F has no engine rows for VM-free steps (T1's STATE segments: receipt 0, the
  forwards, the post-receipt steps), so `EngHalfRC` for STATE has no AIR to prove it from. The split
  instance and the glue are stated (`SplitC` header): `W` = working-set root, `Q` = the `SREQ`/`HB`
  requests, `qOf` = the steps' overlay requests; lane F's side of the glue `ReqsFaithful` (the
  overlay after the step(s) is the overlay before updated by exactly `qOf`) is open, lane B's
  side `ApplyFaithful` is a named premise; `glue_of` composes them.

## Open (M5-T1 list, updated)

1. ~~MSG/DG row lemmas, RNG bus fact~~ (F-2); ~~enter view contract~~ (F-3: `enter_relC` from
   the circuit + named checks); resume: F3-1 (split with lane B, accumulator appends, `estepO`
   composition); enter's `EntChecks.prepaid` / `code` (join with the receipt rows); STATE engine
   rows (none yet); F3-2 (clear-field convention, lane E / owner).
2. **Template coverage**: one FunctionCall per V1 action receipt, ED25519 signer, no inputs/outputs,
   successful call without promises, ≤ 4 non-empty logs, refund > 0, receiver exists with a local
   contract; account-id validity (`AccountId.valid`) and `softExceeded` (recorder size) not in the
   rows; the refund's forward-vs-buffer decision (congestion, bandwidth) is M5c's.
3. **Stand-ins**: `XTAPE` (lane A's call, lane B's account read/write) is public on T1 → M6.
4. Proof size: the `RX` split (above).
