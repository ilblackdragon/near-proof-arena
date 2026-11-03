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
