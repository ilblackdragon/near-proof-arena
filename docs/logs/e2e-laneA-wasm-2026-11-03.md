# E2E lane A (Wasm), 2026-11-03: M1-a, M1-b, M3, M2 corpus coverage

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §5 (owner adopted D-1..D-7 the same day).
Details and logs:
* `research/near-compression/e2e-general/m1/README.md` (section "Update 2026-11-03");
* `research/near-compression/e2e-general/m3/README.md`;
* `research/near-compression/e2e-general/m2/README.md` (second session).

No Lean spec, checker or signed file changed. `make pin-check` ok.

## M1-a: `read_register` writes linear memory

* **AIR.** `wasmBaseIfRegAir` (`wasm-base-lean/WasmBase/RegMem.lean`) is a new AIR value:
  base + HOST' + HOSTO + HOSTT + HOSTB + IF + REG'.
  * **REG' write rows** use STORE's shape on `ptr + pos`.
  * **Bus 211** binds each write group to a successful `read_register` HOST row (`rr = [hid = 49]`,
    is-zero gadget).
* **Two holes found and closed.**
  * A REG read row did not have to consume (`fresh` was free on reads), so register bytes could be
    forged. Now `act·rd·(1−fresh) = 0`.
  * The arity-0 result gap: the public result limbs are now 0 unless returned.
* **T2 `d3tiny.run("hello")`.**
  * CHECK OK; `value_return` on HOSTB is `68656c6c6f`, the chunk's.
  * Proof verifies: 1,474,766 B, 268.2-bit, prove 18.1 s, verify 29 ms, 8 threads.
  * Tamper **136/136 rejected**. The cases cover wrong return bytes, wrong host answers, forged
    register bytes, skipped and orphan writes, `rr` forgery, pointer and time witnesses, and
    `pub.result`.
  * One gap is reported, not counted: a consistent HOST + HOSTO `g_after` change verifies (the
    oracle is free until M6).
* **Lean** (`WasmBase/Main/RegMemLink.lean`, `AxiomsRegMem.lean`; standard axioms, no `sorry`):
  * `writeBytes_facts`;
  * `read_register_run`: the spec's post-state is `writeBytes s4 ptr d`;
  * `heap_read_register`;
  * `regw_write_msgs`: a write row's CH messages;
  * `read_register_rows_heap`: the group's produced messages are the spec post-state's heap entries;
  * `regw_pub_result`;
  * `regw_time_lt`: the algebraic step of `mtp < ts`.
* **Open.** The REG walk and R16 send bound are not yet re-instantiated at the new AIR's index 27.

## M1-b: storage bytes on HOSTB

* Storage key bytes are on HOSTB for `storage_read/write/remove/has_key`.
* `storage_write` also puts its value bytes there, with wire id `hid + 256`.
* Both are request groups with the MEMIO link.
* T2 carries key `74` and value `68656c6c6f`.

## M3: the chunk's own host tape

* **Tape.** `wasmbase-tape` wraps the checker's compiled Wasm entry at link time
  (`-Wl,--wrap` + `tape_shim.c`). The wrapper:
  * returns the real result unchanged;
  * replays each call with the spec's `step` from the checker's own context and trie-backed store;
  * records the host answers.
* **Corpus run.** Over d3c7–d3c10: 19,007 cases, all `accept`, and 27,197 Wasm calls.
  * Replay mismatches: 0.
  * **3,414 / 3,414** calls the AIR covers equal the chunk's outcome when traced with their own
    answers (status, burnt gas, logs, return).
  * This includes **1,755 / 1,755** `d3tiny` calls, and T1 and T2. T1 is the evicted
    `storage_write` path.
* **T1 proof.** T1 with its chunk tape proves (1,476,278 B, verify 50 ms).
* **Coverage.** 23,317 calls are outside `checkModuleIfH` (M2).

## Builds

* `lake build WasmBase wasmbase-tool` is green.
* `build-tape.sh` (`wasmbase-tape`) is green; it builds the needed `spec/lean/v3` Successor
  modules, unchanged.
* The release `nearproof-wasm-base` is green.

## M2 (second session): corpus coverage at `wasmBaseM2Air`

* **Census** (`wasmbase-tool census`): the uncovered calls need wrap/extend, `if` with a result,
  `unreachable`, `ed25519_verify`, and in `d3rich` also `memory.grow`, `abort` (`i32` params) and
  `promise_yield_resume` (`i32` result). No discarding branch, `call_indirect`, bulk memory or
  float occurs in d3c7–d3c10, so those were not built (T3 work).
* **Built.** `checkModuleM2`; `wasmBaseM2Air` = tables 0–26 of `wasmBaseIfRegAir` + REG-C (27,
  register refill) + CONV (28) + UNREACH (29). Instructions the HOST row or the memory model cannot
  carry (`memory.grow`, `memory.size`, `abort`, `promise_yield_resume`) are admitted with opcodes
  no chip can fetch, so a run that executes one is not provable (sound, incomplete).
* **Sweep** (19,007 cases, 27,197 calls, 0 replay mismatches, **0 different**): 21,438 equal +
  4,480 equal-abort = **25,918 / 26,731** method calls; every call of `d3tiny`, `3b1ad423`,
  `e1fe4f9c`, `d3ed`, `d3hostx`; 17,409 / 18,222 of `d3rich`. Remainder 813 (`d3rich.run`):
  `memory.grow` 385, `abort` 120, `promise_yield_resume` 58, stack-budget trap 124, address
  `≥ 2^27` 89, out-of-gas at a Wasm instruction 37.
* **Mutants**: CONV/UNREACH/REG-C, 37 / 37 rejected over three corpus calls (one with a refill, one
  ending in `unreachable`); the full battery at `wasmBaseM2Air` on the refill call, 211 / 211
  (plus the documented HOSTO `g_after` gap, reported not counted).
* **Lean** (`propext`/`Classical.choice`/`Quot.sound` only, no `sorry`): `Main/M2Link.lean`
  (`conv_row_spec`, `step_conv`, `execNum_conv`, `unreach_row`, `regc_clear_cancels`,
  `regc_clear_next`); `Main/RegWalkG.lean`: the REG group walk, `pos < len` and `RegLenAgree` for any
  AIR carrying REG's constraints, instantiated at index 27 of `wasmBaseIfRegAir` and
  `wasmBaseM2Air` (item 2's walk half).
* **Host note.** The shared `zkbuild.slice` sat above its `memory.high` (sibling scopes held
  ~41 GB), which throttled every job in it to near zero (the first sweep under `heavy` stalled for
  40 min). The final builds, sweep and mutants ran in their own `systemd-run --user --scope` with
  `MemoryMax` 16–24 G, `MemorySwapMax=0`, `taskset` 8 CPUs.
* `spec/lean/v3` default `lake build` green; `wasm-base-lean` `lake build WasmBase wasmbase-tool
  wasmbase-tape` green; `make pin-check` ok. No Lean spec, checker or signed file changed.

## Next

* R16 send bound for `wasmBaseIfRegAir`/`wasmBaseM2Air` (then `mtp < ts` and `RegWalkG`'s `hsend`
  are theorems about `Holds`).
* An M2 `Ctx` + row-to-step dispatch (`wasm_base_sound` for M2).
* `d3rich` remainder: `memory.grow` chip, `i32` host tags, stack-budget and out-of-gas abort rows,
  the `2^27` address range.
* Force a clear before every refill (absent-register messages) before M6 binds fill bytes.
* M4 (segment cuts): not started this session.
* M6: replace HOSTO.
