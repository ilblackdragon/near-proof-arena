# E2E milestone M2: Wasm coverage of the d3c7–d3c10 corpus

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §4 (M2) and §5. Date 2026-11-03. Labels: **[M]**
measured here, **[K]** kernel-checked Lean (standard axioms only), **[S]** stated only.

## 1. Census: what the uncovered calls actually need

M3 left 23,317 of 27,197 corpus calls outside `checkModuleIfH`. `wasmbase-tool census <wasm>
<export>` (`wasm-base-lean/WasmBase/Census.lean`) lists, per function of the export's closure, every
reason the checker rejects it. Over the four uncovered codes:

| code | calls | rejected by (`checkModuleIfH`) |
|---|---|---|
| `fbc015a8` `d3rich` `run`/`cb` | 18,028 | `i32.wrap_i64` ×4, `i64.extend_i32_u` ×9, `if (result i32)` ×1, `unreachable` ×1, `memory.grow` ×1 (and its linear fee), `abort` (a host with `i32` parameters) |
| `e1fe4f9c` `run` | 4,048 | `i32.wrap_i64`, `i64.extend_i32_u` ×6, `if (result i64)` ×3 |
| `3b1ad423` `run` | 1,114 | `i32.wrap_i64`, `i64.extend_i32_u` |
| `b192c679` `d3ed` `run` | 127 | the `ed25519_verify` host is not in the host table |

**No discarding branch, `call_indirect`, bulk memory or float occurs in the corpus**: once the
above are admitted, every successor obligation (`verifyAtM2`) holds on every function of every
corpus closure (the census reports no `verify:` failure). Those three features are needed for
compiled Rust contracts (plan target T3), not for d3c7–d3c10; they are not built here (§6).

## 2. What was built

### Checker: `checkModuleM2` (`WasmBase/M2Check.lean`)

`checkModuleIfH` extended without touching it:

| extension | how it is proved |
|---|---|
| `i32.wrap_i64`, `i64.extend_i32_s`, `i64.extend_i32_u` | the CONV chip |
| `unreachable` | the UNREACH chip (a trapping row, `halted = 2`) |
| `if` with one result | checker only: `.else_` must leave exactly `label.height + arity` (no discard) and the else body restarts at `label.height`; the IF/CTRL rows are unchanged (`ifStepM2_result_else` [K]) |
| `ed25519_verify` | host id 61 (fresh), `(6, 1)`, all `i64`, answered by HOSTO like every other oracle host (`hostFnsM2_ids_nodup`, `ed25519_sig_agrees` [K]) |
| `memory.grow`, `memory.size`, a listed host the HOST row cannot carry (`abort`: `i32` parameters) | **admitted, no chip**: records with opcodes `0x240`/`0x241`/`0x242`, which no chip's FETCH query can produce. No satisfied trace passes through such a pc, so a proof covers exactly the runs that do not execute it (sound, incomplete). The trace generator refuses a run that reaches one (`unchipped`) |

`wasmbase-tape` (M3) now uses `checkModuleM2`; `wasmbase-tool prepM2` is `prepIf` with it.

### AIR: `wasmBaseM2Air` (`WasmBase/M2Air.lean`)

```
wasmBaseM2Air = base (0–21) ++ [HOST' (22), HOSTO, HOSTT, HOSTB, IF (26), REG-C (27), CONV (28), UNREACH (29)]
```

Tables 0–26 are `wasmBaseIfRegAir`'s (`m2_air_prefix`).

* **CONV** (18 columns). One-hot `f_wrap, f_extu, f_exts`; consumes the top of the stack with tag
  `f_wrap` and produces at the same slot, tag `f_extu + f_exts`, the limbs
  `[a0, a1, 65535·sgn·f_exts, 65535·sgn·f_exts]`. An extend's input has zero upper limbs; for
  `extend_s`, `a1 = 2^15·sgn + rl` with `r16 (2·rl)`.
* **UNREACH** (8 columns). Receives the state, charges the record's fee, sends `halted = 2`.
* **REG-C** = REG' + `clr` (**register refill**, plan item "register refill"). A **clear group**
  is a read group (`rd = 1`, so every row consumes the live message, `cReadFresh`) whose
  re-production is cancelled by two extra receives of the same messages at the same time
  (`count · clr`). Its length row must be followed by an active fill row of the same register,
  time and host id (`cClrNext*`). So an overwrite consumes the old bytes and old length, then the
  fill produces the new ones. REG' 's constraints and interactions stay a prefix.

### Trace generator and tools (`native/wasm-base`)

* `tracegen.rs`: CONV and UNREACH rows; a refill emits the clear group before the fill (before, it
  panicked); the unchipped opcodes panic with `unchipped opcode`.
* `check-tape`: only **successful** host calls' payloads are outputs (a `log_utf8` that aborts on
  bad UTF-8 still reads its bytes), and an empty `value_return`/`log_utf8` is the empty string.
* `tamper`: CONV, UNREACH and REG-C cases; `TAMPER_ONLY=CONV,UNREACH,REGC` runs only those.
* `m3/sweep.py`: `--air` (default `airM2`); aborted calls also compare logs and the trace's final
  budget with the spec replay's (`g_final`); a run that reaches an unchipped instruction is class
  `unchipped`.

## 3. Results [M]

```sh
research/near-compression/wasm-base-lean/build-tape.sh     # wasmbase-tape (checkModuleM2)
research/near-compression/e2e-general/m3/run.sh OUT /data/illia/nearproof-deps/corpora/d3c{7,8,9,10}/d3
```

The M3 sweep at `wasmBaseM2Air` over d3c7–d3c10 (`logs/summary.json`, binaries in
`logs/SHA256SUMS`): 19,007 cases, all `accept` as unwrapped; 27,197 Wasm calls; 0 replay
mismatches; **0 calls different**.

| class | M3 (`wasmBaseIfRegAir`) | **M2 (`wasmBaseM2Air`)** |
|---|---|---|
| equal (status, burnt gas, logs, return) | 3,414 | **21,438** |
| equal-abort (status, logs, trace final budget = spec's) | – (not compared) | **4,480** |
| different | 0 | **0** |
| outside the checker | 23,317 | **0** |
| reaches an admitted-but-unchipped instruction | – | 563 |
| trace generator out of domain | 0 | 250 |
| no method run | 466 | 466 |

So 25,918 of the 26,731 calls that run a method are in the proved domain and equal: **every**
call of every contract other than `d3rich` (8,509 calls of `d3tiny`, `3b1ad423` incl. `run`,
`e1fe4f9c`, `d3ed`, `d3hostx`), and 17,409 of `d3rich`'s 18,222.

| code | equal | equal-abort | remainder |
|---|---|---|---|
| `d3tiny` `8152bed2` | 1,755 | – | – |
| `3b1ad423` | 2,382 | 25 | – |
| `e1fe4f9c` | 3,434 | 614 | – |
| `d3ed` `b192c679` | 51 | 76 | – |
| `d3hostx` `f1c929ab` | 172 | – | – |
| `d3rich` `fbc015a8` | 13,644 | 3,765 | 813 |

**The remainder (all `d3rich.run`, `logs/remainder.txt`), with reasons:**

| calls | reason |
|---|---|
| 385 | executes `memory.grow` (op 38): admitted, no chip (§6) |
| 120 | executes `abort` (pc 547): `i32` parameters, the HOST row's argument tags are `i64` |
| 58 | executes `promise_yield_resume` (pc 737): `i32` result, the HOST row pushes `i64` |
| 124 | traps on the stack budget (`$rec` recursion): the budget trap has no row ("stack budget exhausted: the trap is not provable", pre-existing generator domain) |
| 89 | `MemoryOutOfBounds` at an effective address `≥ 2^27`: LOAD/STORE carry `e1 < 2^11` (pre-existing address domain) |
| 37 | `GasExceeded` at a Wasm instruction's charge (not at a host call): no row for the gas-exhaustion abort (34 reported as `host event`, 3 as `spec run did not finish normally`) |

What "equal-abort" compares: for an aborted call the outcome's burnt gas is the host's abort
accounting (`burn`, `GasExceeded` caps, `used` vs `burnt`), which the Wasm trace does not carry; the
trace's claim is its final budget, which equals the spec replay's (`prep.gFinal`), and the logs
equal the chunk's. For a `promise_return` (outcome `receiptK`) the trace's last return-kind call is
`promise_return` with its promise index; the receipt numbering is the state side's (M5b/M6).

Two comparison fixes found on the way, both in the sweep's reading of the trace, not in the AIR:
`log_utf16` payloads (UTF-16LE, stored by the outcome as UTF-8) and payloads of host calls that
abort (a `log_utf8` with bad UTF-8 reads its bytes but logs nothing).

## 4. Mutants [M]

`TAMPER_ONLY=CONV,UNREACH,REGC nearproof-wasm-base tamper <airM2> <prep>`: each case is re-proved
and natively verified (`logs/*-tamper.log`). The honest proof verifies and its `code_root` matches
in all three.

| call (from the sweep) | cases | rejected |
|---|---|---|
| `e1fe4f9c.run` (wrap; 24 steps) | CONV wrap `a0`/`a1`/`ta`+1, wrap-as-extend_u, all flags 0; REG-C spurious clear on a read | **6 / 6** |
| `3b1ad423.run` (wrap, extend_u, a **refill** of register 0; 96 steps) | CONV wrap and extend_u (5 each); REG-C: clear byte/len with `clr = 0`, clear byte+1, clear len+1, the following fill's `rid`/`ts`+1, spurious clear | **17 / 17** |
| `d3rich.run` ending in `WasmTrap(Unreachable)` (259 steps) | CONV wrap and extend_u (5 each); UNREACH `act = 0`, `fee`+1, `pc`+1; spurious clear | **14 / 14** |

**37 / 37 rejected.** `extend_s` occurs in no corpus run, so its sign-bit case (`CONV[f_exts] sgn
flip`) has no target here; `conv_limbs`/`conv_row_spec` cover it in Lean.

**Full battery at `wasmBaseM2Air`** on the `3b1ad423.run` refill call (`TAMPER_ONLY` unset: every
pre-existing base, HOST, HOSTB, REG' case plus the new ones; `logs/refill-full-tamper.log`):
**211 / 211 rejected**. The one reported gap is the known one, not counted: a consistent HOST +
HOSTO `g_after` change verifies (the oracle is free until M6).

## 5. Lean [K]

* `WasmBase/Main/M2Link.lean`:
  * spec side: `extendS_64_32`, `execNum_conv` (the three conversion arms are `convVal` of the
    popped value), `exec_unreachable`;
  * `conv_limbs`: CONV's output limbs and tag are those of `convVal op v`;
  * `conv_row_facts`, `conv_row_cons`, `conv_row_prod`, **`conv_row_spec`**: an active CONV row whose
    R16 query `2·rl` is 16-bit, consuming `enc 0 i v tp`, produces `enc 0 i (convVal op v) ts` with
    `op` the opcode of its FETCH query;
  * **`step_conv`**: the spec step of a conversion from a `RelW` state consumes the top message and
    produces `enc 0 (n−1) (convVal op v) t` — the same message;
  * `unreach_row`: no CH traffic, `halted = 2`;
  * `regc_clear_cancels`, `regc_clear_next`: a clear row consumes and leaves nothing on space 6; a
    clear group is followed by the fill of the same register, time and host.
* `WasmBase/Main/RegWalkG.lean` (generated from `RegWalk.lean` by `mkwalkg.py`): the REG group walk,
  `pos < len`, `gap < 2^16` and `Register.RegLenAgree` for a group, for **any** AIR `A` with
  `RegAt A ti` (table `ti` contains REG's constraints and interactions; only RANGE16 answers R16).
  Instances: **`regAt_ifreg`** (`wasmBaseIfRegAir`, index 27) and **`regAt_m2`** (`wasmBaseM2Air`,
  index 27, REG-C). So the walk is a theorem about `Holds` of the current AIRs.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`.

**Named open.**
* The per-bus R16 send bound (`hsend`) for `wasmBaseIfRegAir`/`wasmBaseM2Air`. `RegWalkG`'s
  gap/`pos < len` lemmas and the `mtp < ts` of REG' write rows (`regw_time_lt`) take it as a
  hypothesis, as `RegWalk` did before `RegSend`. Discharging it is `RegSend.lean`'s argument over the
  new tables (HOST' and REG-C keep HOST's and REG's R16 interactions as prefixes; the new R16 counts
  are `act·(1−kind)·wr`, `act·kind·wr`, `act`, `f_exts`, all products of constrained bits).
* An M2 `Ctx` and the row-to-step dispatch over the 30 tables (`wasm_base_sound` for M2):
  `step_conv` takes the M2 checker's successor facts as hypotheses.
* Forcing a clear before a refill: nothing yet stops a prover from filling a live register
  without clearing it (two messages in its slots). Today this is inside the HOSTO oracle gap (fill
  bytes are oracle answers until M6). The fix is an "absent" length message per register id
  produced once at the start (distinct, sorted ids) that every fill consumes; a clear re-produces it.

## 6. Not done here

* `memory.grow`/`memory.size` chips: memory size is the public `pubMem`, used by LOAD/STORE's bound
  check, so a sound grow needs a dynamic size (a channel message consumed by LOAD/STORE) or
  MEMINIT rows timed at the grow for the new pages; both change base tables 11, 12, 19.
* `call_indirect` (cached TABLE), bulk memory, kill rows for discarding branches, floats: not used
  by the corpus (§1); needed for T3.

## Update: R16 send bound

`WasmBase/Main/RegSendM2.lean` closes the first "named open" item of §5 (standard axioms only, no
`sorry`):

* **`ifreg_hsend_r16`**, **`m2_hsend_r16`**: from `Holds (wasmBaseIfRegAir …)` /
  `Holds (wasmBaseM2Air …)` and `PubOK X nloc ngl pub`,
  `∀ o ∈ occs A tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1`.
  Tables 0–21 go through `occ_bits_of` (as in `RegSend`); tables ≥ 22 go through one decidable check
  (`R16Ok`: every R16 send count is syntactically a product / `1 − ·` of `bool`-constrained
  expressions of that table, `bitE_sound`), `decide`d against the actual interaction lists of HOST',
  HOSTO, HOSTT, HOSTB, IF, REG', REG-C, CONV and UNREACH.
* The walk without `hsend`: `ifreg_/m2_reg_gap_lt` (`gap < 2^16`), `ifreg_/m2_reg_pos_lt_len`
  (`pos < len`), `ifreg_/m2_regLenAgree_group` (`Register.RegLenAgree` for a group, same remaining
  hypotheses as `regLenAgree_group_of_holds`: group start, `rid ≤ 99`, `pos < 2^24`, active length row).
* **`ifreg_regw_mtp_lt_ts`**, **`m2_regw_mtp_lt_ts`**: on a REG'/REG-C byte row (`kind = 0`) with
  `wr = 1`, `mtp < ts`, given `ts < 2^29` and `mtp < 2^29` as explicit domain hypotheses
  (`regw_time_lt` through the R16 lookup of the row's `timeChk`; generic form `regw_mtp_lt_tsG`).

Still open from §5: the domain bounds `ts, mtp < 2^29` are hypotheses (not derived from the AIR),
the M2 `Ctx`/row dispatch, and forcing a clear before a refill.

## Update: M2 soundness (2026-11-03)

Plan item "full soundness theorem for `wasmBaseM2Air`: successor facts from the checker, not
hypotheses". Delivered: steps 1–2 (the context, and the CONV/UNREACH rows, non-vacuously). **Not**
delivered: the 30-table dispatch and `wasm_base_sound_m2`. All [K]. Axioms are `propext`,
`Classical.choice` and `Quot.sound` only, with no `sorry`.

**Step 1: `WasmBase/M2Ctx.lean`.** `M2Ctx` carries `hM : checkModuleM2 cfg p fn = some MH`, and every
code fact is derived from it:
* `checkM2_sound`/`CheckFactsM2` and `checkModuleM2_sound`/`ModFactsM2`;
* the accessors `factsOf`, `recG`, `loc_unique`, `off_bound` and `maxFee_ge`;
* the successor facts: `M2Ctx.conv_succ` (exactly `step_conv`'s `hstk`/`hnext`/`hL1`/`hH1`),
  `M2Ctx.if_succ`, `M2Ctx.ifres_succ` and `M2Ctx.else_succ`;
* the records `M2Ctx.conv_record`/`unreach_record`;
* the FETCH converse `recordAtM2_conv_op`/`recordAtM2_unreach_op`/`M2Ctx.recG_conv`/`recG_unreach`.
  A record with opcode 0xA7/0xAC/0xAD, or 0x00, is the record of that instruction.

**Step 2: `WasmBase/Main/M2Rows.lean`.** It works against `Holds (wasmBaseM2Air …)` itself, using
that AIR's own bus balance and not the base AIR's:
* lookups: `m2_fetch` (FETCH soundness; all 29 non-CODE tables only send on FETCH), `m2_r16` and
  `m2_time_chk`, plus the FETCH pins `m2_fetch_conv`/`m2_fetch_unreach`;
* `conv_row_m2`: an active CONV row's pc is a checked `(k, pc)` with `code[pc] = .num op`
  (`op = convOpN`, `isConvOp op`), and its fee and height are the pc's. Its CH effect is `convVal op` of
  the consumed value (`conv_row_spec`, with the R16 bound from the lookup). It also gives `halt0`,
  `tsOut`, `gasOut`, `consT`, `prodT` and `prodNd`;
* `unreach_row_m2`: the same pin with `.unreachable`, no CH traffic, `halted = 2`, and
  `halt0`/`tsOut`/`gasOut`;
* the spec side over `M2Ctx`: `M2Ctx.step_eq_exec`, `step_conv_spec` and `step_unreach_spec`;
* the joins: `conv_row_step_m2` (the spec step continues, and the row's produced message is the new
  stack top at the same slot) and `unreach_row_step_m2` (the spec step aborts with
  `WasmTrap(Unreachable)`).

Named hypotheses:
* `hsendF`: FETCH send counts are ≤ 1, the same kind of fact as `hsend`;
* `hsend`: the R16 bound, being proved in `RegSendM2.lean`;
* `CodeOKM2`: the commitment binding of the CODE table to the M2 records, as `CodeOK` is for the
  base records.

**The `Ctx` split (done).** `Ctx.hM` is now `ModFacts cfg p fn M` (moved to `CheckFacts.lean`)
instead of `checkModule cfg p fn = some M`. Its per-function `CheckFacts` state the base obligations
(`verifyAt`, `recordOf`) only at pcs that are not M2 additions (`m2Special`: conversions,
`unreachable`, `if`, `else`, `memory.grow`/`size`, import calls). Both checkers produce it:
* `checkModule_sound` / `Ctx.ofCheck` for the base checker;
* `checkModuleM2_modFacts` / **`M2Ctx.toCtx`** for the M2 checker (`verifyAtM2_base`,
  `recordAtM2_base`: off the M2 pcs the M2 obligations and records are the base ones).

The base step lemmas discharge `m2Special = false` locally (their instruction is known; `m2_ns`),
and `verify_call` takes `imports.size ≤ fi`. One premise is new: **`Ctx.Base`** (no checked pc is an
M2 addition), as `Looks.base`, and so as `hB : X.Base` of `looks_of`, `wasm_base_exec`,
`wasm_base_sound`, `rowFactsSegMap_of` and `wasm_base_exec_host_holds`. For a base context it is
`Ctx.ofCheck_base`, so those theorems say exactly what they said before. It is used in one place,
`fetch_rec`/`fetch_pc`/`RowCall`, where a fetched record has to be a base `recordOf` record.

The steps, in order:
1. Split `Ctx` into data plus a code-facts predicate that both `checkModule` and `checkModuleM2`
   satisfy.
2. Re-thread the uses of `verify`/`recs` (about 45 sites).
3. Then `RowFacts2` for CONV/UNREACH is `conv_row_m2` plus `step_conv`'s relation update
   (`step_straight`). The dispatch then covers:
   * tables 0–21 of the M2 AIR, through the base `chipFacts`, with FETCH and R16 coming from
     `m2_fetch`/`m2_r16` instead of the base `Looks`;
   * IF (26), through `if_rowSpec`, with `IfRowData` discharged by `M2Ctx.if_succ`/`ifres_succ`;
   * CONV (28) and UNREACH (29);
   * HOST (22), still under `HoldRow`;
   * REG-C (27), with the refill clear/absent gap still open;
   * a STATE/CH bus split of the M2 AIR, because the host stack's `host_buses` covers only tables
     0–22.

## Update: absent-register header (`wasmBaseM2rAir`)

Closes the §5 open item "forcing a clear before a refill", as a **new** AIR value
(`WasmBase/M2RegAbsent.lean`; `wasmBaseM2Air` and REG-C are unchanged):

```
wasmBaseM2rAir = base (0–21) ++ [HOST', HOSTO, HOSTT, HOSTB, IF (26), REG-A (27), CONV (28), UNREACH (29), RINIT (30)]
```

* Per register id exactly one *header* is live: its length message or an **absent** message
  `[6, rid·2^24, 3, 0,0,0,0, tp]` (tag 3). **RINIT** (`act, rid, gap`) produces one per used id at
  time 0, ids strictly increasing (`nxt.rid = rid + 1 + nxt.gap`, `rid`, `gap` R16-checked).
* **REG-A** = REG-C + `atp, ahp`: a fill group's length row (`act·kind·(1−rd)`) consumes the absent
  message at `atp ≤ ts` (`r16 (ts − atp − 2^16·ahp)`, `r16 (4·ahp)`; non-strict because a clear and
  its fill share `ts`); a clear group's length row (`act·kind·clr`) re-produces it at `ts`; new
  constraint `cLenAct = (1 − nxt.f)·nxt.kind·(1 − nxt.act)` (a length row after a byte row of its
  group is active — otherwise a fill could create bytes without consuming the header). Leftover
  absent messages go to DRAIN (`space·inv = 1` admits space 6).
* Tools: `wasmbase-tool airM2r <nloc> <ngl>` / `evalM2r`. The trace generator enables the header
  when the AIR has a `RINIT` table (`tracegen.rs` `Absent`); `tamper` adds `REGA`/`RINIT` cases.

**Lean [K]** (`WasmBase/Main/M2RegAbsentFacts.lean`, standard axioms): `regAt_m2r` (the group walk
applies at index 27), `m2r_hsend_r16` (R16 send bound), `m2r_regLenAgree_group`; header row facts
`m2r_fill_consumes_absent`, `m2r_fill_absent_time` (`atp ≤ ts` for times `< 2^29`),
`m2r_clear_produces_absent`, `m2r_rinit_produces_absent`, `m2r_lenAct`, `m2r_rinit_prefix`,
`m2r_rinit_strict`, `m2r_rinit_distinct`. **Open:** the bus-level count (per id,
`#fills ≤ 1 + #clears`, hence one live length message) needs the CH decomposition of the M2 tables
(only RINIT/REG-A/DRAIN carry space-6 tag-3 messages; DRAIN's and LOCAL's space/tag are columns).

**Measured [M]** on the refill call `3b1ad423.run` (`refill.json` of §4; 96 steps, a refill of
register 0). Honest: `check-tape` passes at `wasmBaseM2rAir` with the same outcome as at
`wasmBaseM2Air` (also `conv.json`, `unreach.json` of §4). Mutants (`logs/refill-m2r-*.log`):

| mutant | `wasmBaseM2Air` | `wasmBaseM2rAir` |
|---|---|---|
| double fill: the clear group made a plain read (`clr = 0`) and its re-produced messages drained, so the fill overwrites a live register | **verifies** (precheck passes; `logs/refill-m2-doublefill-gap.log`) | rejected: absent `(rid 0, t 71)` consumed, never produced |
| same, the fill claiming the RINIT message (`atp = 0`, R16 answers adjusted) | – | rejected: absent `(rid 0, t 0)` consumed twice |
| fill `atp + 1`; fill length row `act = 0` (`cLenAct`) | – | rejected (bus; constraint) |
| RINIT `act = 0`; `rid + 1` | – | rejected (bus) |
| RINIT duplicate id / unsorted ids (`cInc` satisfied in the field by `gap = p − 1`, `p − 2`; extra absent drained, `rid` answered) | – | rejected by the R16 lookup on `gap` |

`TAMPER_ONLY=REGA,RINIT,REGC,CONV` at `wasmBaseM2rAir`: **25 / 25 rejected** (the pre-existing
REG-C and CONV cases included); header-only rerun after the `atp = 0` case was made R16-clean: 8 / 8.
**`RowFacts2` for CONV and UNREACH (done).** `conv_rowfacts_m2` and `unreach_rowfacts_m2` [K] give
`RowFacts2 X.toCtx …` for the active rows of `Holds (wasmBaseM2Air …)`. For CONV the spec part is
`step_conv` on the base `RelW`, with the successor facts from `M2Ctx.conv_succ`; for UNREACH it is
the abort with the segment gas. Named hypotheses: `hsendF`, `hsend` and `CodeOKM2`. `hsend` is
`m2_hsend_r16` (`RegSendM2.lean`), but that lemma takes a `PubOK X` for an `X : Ctx`, so it applies
with `X := M2.toCtx`.

**Still open, in order:**
1. **`Looks.base` off for M2 contexts.** For an M2 trace, `fetch_rec` must get "base record" per
   row, not from `Ctx.Base`. Two parts:
   * a FETCH opcode separation for each of the 14 instruction tables: under its constraints an
     active row's opcode is in the chip's own set, which avoids 0, 0xA7/0xAC/0xAD, `opIf`, `opHost`
     and 0x240–0x242;
   * an `.else_` arm in `RowCtrl`, because CTRL's jump opcode `opJump` *is* the M2 `else` record's
     opcode. `step_else` (`StepIf.lean`) and `M2Ctx.else_succ` are the ingredients.
2. **The base row lemmas on an M2 trace.** They take `H : Holds (wasmBaseAir …)` and `Looks` over
   the base AIR's occurrences. The M2 AIR's FETCH and R16 lookups are `m2_fetch`/`m2_r16`; BYTE
   and FUNC need the same recv-only argument over the 30 tables. The row lemmas use `H` for their
   constraints, which hold on an M2 trace (tables 0–21 are a prefix), but `H` itself (the base
   balance) does not follow from the M2 `Holds`. The host stack works around this with `H0`.
3. **IF (26).** Use `if_rowfacts`, discharging `IfRowData` from `M2Ctx.if_succ`/`ifres_succ` and an
   `opIf` FETCH pin (`recordAtM2`'s `.if_` arm).
4. **The STATE/CH bus split of `wasmBaseM2Air`** (the analogue of `host_buses`, which covers tables
   0–22). The instruction rows are those of tables 1–14, 22, 26, 28 and 29, with the REG-C, HOSTO,
   HOSTT and HOSTB contributions.
5. **The dispatch and `wasm_base_sound_m2`** over `exec_of_rows_seg`. `HoldRow` (HOST), the HOSTO
   answers and the REG-C refill gap stay as named hypotheses.

## Update: coverage chips for the admitted-but-unchipped instructions (`wasmBaseM3Air`)

A new AIR value (`WasmBase/M3Air.lean`) on top of `wasmBaseM2rAir`; every existing table and AIR is
unchanged:

```
wasmBaseM3Air = base (0–21) ++ [HOST-W (22), HOSTO, HOSTT, HOSTB, IF, REG-A (27), CONV, UNREACH, RINIT (30),
                                MEMG (31), MSZ (32), GINIT (33)]
```

* **HOST-W** (`i32` host signatures: `abort`, `promise_yield_resume`): HOST' with the argument tag
  `tagP j = pf j·(1 − ti j)` and the result tag `1 − ri` instead of the fixed `1`; an `i32` argument
  or result has zero upper limbs; `tmask = Σ 2^j·ti j` and `ri` go into the HOSTT lookup
  `[hid, np, ar, tmask, ri, 0, 0, 0]`, so the statement's host table (`hostRowM3`, from the spec's
  `hostSigs`) fixes them per host. For all-`i64` hosts the table row is the M2 one.
* **Memory size as a channel message** (space 8; space 7 is the segment AIR's gas register):
  **MSZ** produces `[8, 0, 0, pages, …, 0]` at time 0 (`65536·pages = pubMem`, only row 0 active);
  **MEMG** (`memory.size` 0x3F, `memory.grow` 0x40) consumes and re-produces it. A grow pops `n`
  (`i32`, `n < 2^27`) and either succeeds (`old + n + d = 2048`) or fails
  (`old + n = 2049 + e`, pushes `2^32 − 1`). `S` advances by `fee + lin·n`, which is
  `charge`'s linear fee in units of `R`. `lin` is record field 4; PV86 has
  `linearOpUnitCost = regularOpCost`.
* **GINIT**: a grown byte's channel message `[3, ad, 0, 0…, tg]` is produced at the grow's time,
  one row per touched grown byte, addresses strictly increasing, in a range `[65536·old, 65536·new)`
  that a successful MEMG row offers on bus 213 (multiplicity `gm`, with `gm·(1 − ok) = 0`; without
  that constraint a padding row's free message would let a GINIT row create a byte anywhere at any
  time). LOAD/STORE stay unchanged: in bounds = the message exists, and a grown byte's message only
  exists from the grow on.
* **`checkModuleM3`** (`WasmBase/M3Check.lean`) emits chip records instead of the M2 no-chip ones
  (`0x242` → HOST-W's `0x1FF`, `0x241` → `0x3F`, `0x240` → `[pc, 0x40, h, c/R, lin, 0, 0, 0]`) and
  requires `cfg.maxMemoryPages = 2048`. Tools: `wasmbase-tool airM3/evalM3/prepM3`,
  `WASMBASE_TAPE_CHECKER=M3 wasmbase-tape`.
* `abort`'s message is an output: the trace now moves its two length prefixes and UTF-16 strings on
  HOSTB (request groups `51 + 256·k`). `check-tape` reports `abortx` and `m3/sweep.py` rebuilds the
  `ABORT: …` log from it, so an `abort` call is compared on its logs too.

**Lean [K]** (`WasmBase/Main/M3Facts.lean`, standard axioms only):
* `regAt_m3`, `m3_hsend_r16` (via `hsend_r16_of_tail`), `m3_regLenAgree_group`;
* HOST-W: `m3_host_arg_tag`, `m3_host_arg_i32`, `m3_host_res_i32`;
* MEMG: `m3_grow_ok`, `m3_grow_fail`, `m3_grow_gm`;
* MSZ: `m3_msz_only_first`, `m3_msz_pages`;
* GINIT: `m3_ginit_range`, `m3_ginit_step`;
* checker: `abort_tags`, `yield_resume_tags`.

`r16 (32·x)` alone does **not** bound `x`: for `x ≈ P/32`, `32·x mod P` can be tiny. So every such
limb in the new tables is also checked as `r16 x` (`m3_col32_lt` takes that premise).

**Measured [M]** — the M2 remainder: the M3 tape (`WASMBASE_TAPE_CHECKER=M3`) over the 798 cases
holding the 813 remainder calls, then `sweep.py --air airM3`
(`logs/m3-remainder.txt`, `logs/m3-remainder-summary.json`, script `m3rem.py`). The full d3c7–d3c10
sweep was **not** rerun at M3; the other 1,289 calls of those 798 cases stay equal / equal-abort.

| M2 remainder reason | calls | at M3 |
|---|---|---|
| `memory.grow` (0x240) | 385 | **378 equal** (311 equal + 67 equal-abort); 7 now stop at a pre-existing limit (4 stack budget, 2 address ≥ 2^27, 1 GasExceeded) |
| `abort` (0x242, pc 547) | 120 | **120 equal-abort** (status, final budget and logs incl. the `ABORT:` message) |
| `promise_yield_resume` (0x242, pc 737) | 58 | **57 equal** (47 + 10 equal-abort); 1 stack budget |
| stack budget exhausted (pre-existing) | 124 | 124 (unchanged) |
| effective address ≥ 2^27 (pre-existing) | 89 | 89 |
| GasExceeded at an instruction charge (pre-existing; 34 reported as `host event`, 3 as spec-not-finished) | 37 | 37 |

**555 of the 813 become equal (0 different).** What is left: 258 calls, all pre-existing
trace-generator limits:
* 129 stack-budget traps;
* 91 effective addresses ≥ 2^27;
* 34 + 4 gas exhaustion at an instruction charge.

**Mutants [M]**: 25 / 25 rejected (`TAMPER_ONLY=HOSTW,MEMG,MSZ,GINIT`). The honest proof verifies in
each run.

| run | cases | rejected |
|---|---|---|
| abort call (`logs/m3-abort-tamper.log`) | `abort`'s argument 0 claimed `i64` with `ti0`, `tagP0` and `tmask` mutually consistent (caught by the HOSTT lookup and the stack tag); `ti0 = 0`; `tmask = 0`; MSZ `pg+1` | 4 / 4 |
| `promise_yield_resume` call (`logs/m3-yield-tamper.log`) | result as `i64` (`ri = 0`); `i32` result upper limb + 1; MSZ | 3 / 3 |
| grow call (`logs/m3-grow-tamper.log`) | claim failure (`ok = 0` with the matching `e`); `d+1`; `old+1`; `n0+1, d−1`; `lin = 0` (skip the linear fee); `gm+1`; MSZ | 7 / 7 |
| `growkat.wat` (`logs/m3-growkat-tamper.log`) — grow 1024 → 1026 pages, stores and loads in the grown pages, an untouched grown byte, a failing grow, `memory.size` | the grow cases; `memory.size` `old+1`; MSZ `pg+1`; GINIT `act = 0`, `tg − 1` (a zero byte before the grow), `ad + 1` | 11 / 11 |

`growkat`'s honest trace has the spec's final budget (`g_final_trace = gFinal`), so the linear fee is
charged exactly.

**Open:**
* the bus-level memory lemma, i.e. that grown bytes are unique and disjoint from MEMINIT's, which
  follows from the size-message chain, GINIT's order and `m3_ginit_range`, but is not composed;
* GINIT's `m3_ginit_range` takes the MEMG-side bounds (`old, new ≤ 2048`) as hypotheses; the bus-213
  lookup soundness that supplies them is not composed;
* a segmented (M4) run with `memory.grow` (the size message would be a hashed live message; not
  tested).
