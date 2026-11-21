# E2E milestone M5-T1 (lane F): the runtime rows of T1's FunctionCall receipt

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §3.3 (Wasm ↔ state join), §4.2 (M5), §5.2 (status).
Date 2026-11-21. Labels: **[M]** measured here, **[K]** kernel-checked Lean (std axioms, no `sorry`),
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

## Open (in order)

1. **`SegSoundRt`** (lane E's `Templates.lean`, merged): the `rt` template's obligation is stated on
   boundary digests (`resume`: the receipt step with the VM answered from the tape). What exists is
   the row level (`rx_rel_of_row` + `SpecLink`); missing: the `MSG`/`DG` row lemmas (the engine walks
   the schema; `Seg` layouts = the spec's encoders, checked on T1 by `tracegen.py` only), the bus
   argument for the `RNG` facts (`Hyps.bytes`), the composition into `CutW.applyActionReceiptW`'s
   monadic step (overlay, recorder), and the boundary digest (`ViewImpl` of RS). `TmplComplete` for
   `rt`: not started.
2. **Template coverage**: one FunctionCall per V1 action receipt, ED25519 signer, no inputs/outputs,
   successful call without promises, ≤ 4 non-empty logs, refund > 0, receiver exists with a local
   contract; account-id validity (`AccountId.valid`) and `softExceeded` (recorder size) not in the
   rows; the refund's forward-vs-buffer decision (congestion, bandwidth) is M5c's.
3. **Stand-ins**: `XTAPE` (lane A's call, lane B's account read/write) is public on T1 → M6.
4. Proof size (relations term), see above.
