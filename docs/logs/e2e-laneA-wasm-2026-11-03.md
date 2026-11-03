# E2E lane A (Wasm), 2026-11-03: M1-a, M1-b, M3

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §5 (owner adopted D-1..D-7 the same day).
Details and logs:
* `research/near-compression/e2e-general/m1/README.md` (section "Update 2026-11-03");
* `research/near-compression/e2e-general/m3/README.md`.

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

## Next

* M2: `memory.grow`/`memory.size`, `call_indirect`, bulk memory, discarding branches.
* REG' walk and R16 at index 27.
* Register refill.
* M6: replace HOSTO.
