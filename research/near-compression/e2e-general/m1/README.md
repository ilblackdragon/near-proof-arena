# E2E milestone 1: a real corpus call's Wasm execution on the main PQ stack

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §4 (M1) and §5. Date 2026-10-31. Labels: **[M]**
measured here, **[I]** inferred from the measurements.

## What M1 does

1. **Pick the call from a chunk, not from a hand-written program.** `extract_calls.py` runs the
   independent clean-room checker (`oracle/tools/spec_check_v3_d3.py`, no Lean code) on a whole
   corpus chunk. It records every VM invocation the chunk's validation makes: code bytes (sha256),
   method, prepaid gas and input, plus the outcome the chunk used (aborted, burnt, logs, return
   value).
2. **Run the Lean spec interpreter on that call.** This is `wasmbase-tool prepIf`, rebuilt fresh
   from this tree.
3. **Compare.** `compare.py` checks status and burnt gas against the chunk's outcome. Burnt gas is
   compared as loading fee plus the spec's Wasm gas. It also checks the `log_utf8` and
   `value_return` bytes that the generated trace carries on `HOSTB`.
4. **Prove and attack.** `run.sh` exports the IF+host AIR (`airIfH`) from Lean, then proves and
   verifies with `nearproof-wasm-base` at the seg-v1 shape. Finally it runs the mutation suite.

```sh
research/near-compression/e2e-general/m1/run.sh <case dir> <call index> <out dir>   # NOPROVE=1: stop after compare/check
```

Builds used:
* `lake build wasmbase-tool` in `research/near-compression/wasm-base-lean`, from `.lake` copied
  (not hard-linked) from the main checkout;
* `cargo build --release --locked --offline -j 8` of `native/wasm-base` into
  `/data/illia/nearproof-deps/e2e-m1/target`.

Binary hashes are in `logs/SHA256SUMS`. Heavy steps ran under `heavy` (16 G) on CPUs 8–15/24–27
with 12 Rayon threads.

## Targets

| id | chunk | call | chunk outcome (clean-room, chunk verdict `accept`) |
|---|---|---|---|
| T2 call 0 | `d3c9/d3/00-h10018-s0` | `d3tiny` (sha256 `8152bed2…`, the repo's `oracle/v3-d3/contracts/d3tiny.wasm`) `run("hello")`, 3 Tgas prepaid, freshly deployed account | burnt 104,421,422,859; log `tiny`; return `hello` |
| T1 call 0 | `d3c8/d3/02-h10196-s3` | the same code, pre-state account, `run("again")`, 54 Tgas, key `t` already present | burnt 121,110,620,829; log `tiny`; return `again` |

## Results

| check | T2 call 0 | T1 call 0 |
|---|---|---|
| eligible for `checkModuleIfH` | yes: 29 code records, 1 `if`, 26 steps | yes |
| AIR pre-check (constraints + every bus) | `CHECK OK` [M] | `CHECK OK` [M] |
| status vs the chunk | **match** (`fin`) | **match** |
| log bytes on `HOSTB` vs the chunk | **match** (`74696e79`) | **match** |
| return bytes on `HOSTB` vs the chunk | **DIFFER**: trace `0000000000`, chunk `68656c6c6f` | **DIFFER**: `0000000000` vs `616761696e` |
| burnt gas vs the chunk | **DIFFER** by 11,400,000,000 | **DIFFER** by 28,089,197,970 |
| real proof (prove + native verify) | **verifies** [M]: 1,469,458 B (whir 1,376,238), 268.2-bit calculator, n_stack 18, prove 35.6 s, verify 0.030 s, 1.37 GB peak | not proved separately (same 26-step path; only input and prepaid gas differ) |
| mutation suite (`tamper`, each case re-proved and natively verified) | **92/93 rejected** [M]; the one accepted is `pub.result+1`. That is the known arity-0 statement gap: `Boundary` gates the result on `pubNres`, and `d3tiny` returns nothing on the stack (`docs/logs/pq-if-air-2026-10-22.md`) | – |

So a real chunk's contract call is now proved on the main stack from its own inputs. **But the
comparison shows that the proved trace is not the chunk's execution in two respects.** These two
findings are M1's main result.

1. **Host → memory writes are not modelled, so the trace returns zeros.**
   * `d3tiny` calls `input` (register 0 ← `hello`), then `read_register(0, 16)` (memory[16..21] ← register 0),
     then `value_return(n, 16)`.
   * On the `airIfH` stack:
     * `input`'s response carries a 4-byte placeholder on `HOSTB` (4 `dir=1` rows, not 5);
     * `read_register` moves **no** bytes into linear memory;
     * `storage_write` puts neither key nor value on `HOSTB` (0 rows);
     * `value_return` therefore reads the data-segment zeros at 16 (`logs/T2-call0-hostb.log`).
   * Every bus balances and the proof verifies. The AIR has no constraint that ties `read_register`
     to memory: REG's `ptr` column is documented as the "deferred MEMIO link"
     (`WasmBase/RegChip.lean`), and `airIfH` has no REG table at all.
   * There is **no AIR on main that has both `IF` and `REG`**. `wasmBaseRegAir` lacks IF;
     `wasmBaseIfHostAir` lacks REG.
   * The earlier "`d3tiny` eligible, replays through the AIR, `CHECK OK`" results
     (`docs/logs/pq-if-air-2026-10-22.md`, `pq-memio-finalized-2026-10-23.md`) are true but
     **overclaim**: what replays is a run with different host memory effects than the spec's
     (the spec run's return is `hello`).
   * The public statement (steps, status, gas units `S`) is unaffected. The proof's Wasm-internal
     values are wrong as soon as the state side consumes them (M6).
2. **Host gas comes from the wrong state.**
   * `prepIf` runs the host functions against the default empty context, not the chunk's.
   * The T2 difference is exactly 5 × 2,280,000,000 = 5 × `read_cached_trie_node`
     (`NearSpecV3/Wasm/TrieAccounting.lean:26`): the chunk's `storage_write` hit trie nodes cached
     earlier in the same chunk [I].
   * T1's key already exists, so the evicted-value path adds more: 28.1 Ggas in total [I for the
     split].
   * The `HOSTO` oracle accepts whatever `gAfter` it is given. The proof is therefore of the default
     context's gas, not the chunk's. The real host answers must come from the chunk run (M3).

## Next steps (in order; each one closes a named finding)

1. **M1-a: an `IF`+`REG` AIR (`wasmBaseIfRegAir`) plus the host → memory write link.**
   * Append `REG` to `wasmBaseIfHostAir` as a new AIR value, so existing indices are unchanged.
   * Give REG's read-byte rows (`rd = 1`, `kind = 0`) the MEMIO write shape: consume the live
     space-3 byte at `ptr + pos` (old value `ob`, producer time `mtp`, `timeChk` witness `hp`) and
     produce the register byte at `ts`. This is `Chips.Load`/`STORE`'s pattern; `ptr` gets two
     16-bit limbs as in `HOSTB`.
   * Bind the rows to a real `read_register` HOST call. The row group's `(ts, hid = 49, len)` must
     match the HOST request, or an orphan byte row could rewrite memory.
   * Lean: extend `RegWalk`/`MemIOLink` with `reg_write_heap` (the heap after the group =
     `writeMem ptr bytes`) and connect it to `step_host_ok` for `read_register`.
   * Rust: tracegen emits the write rows and retimes the memory producers. Fix `input`'s response
     payload to carry the real register bytes.
   * Exit: T2 and T1 `return` match, and the HOSTB/REG tamper cases are rejected.
2. **M1-b: storage request bytes.** `storage_write`'s key and value ranges on `HOSTB`, the same
   MEMIO request shape as `log_utf8`. Exit: the bytes `t` / `hello` appear on the wire.
3. **M3 (already planned): the real host tape.**
   * Feed `prepIf` the chunk's host answers (status, word, `gAfter`, register fills) from the Lean
     `allFeatures` run of the same chunk.
   * Alternatively, run `prepIf` on a `CallCtx`/trie-accounting state reconstructed from the chunk.
     The clean-room run already gives the target values to compare against.
   * Exit: burnt gas matches on T1 and T2 (and on every `d3tiny` call in the corpus: 1,685
     executions).
4. **Pre-existing breakage found while building:** `lake build WasmBase` **fails on main** at
   `WasmBase/HostCtx.lean:547` (`current_contract_code_h`: `hostCall.eq_21` no longer matches after
   `a286d805f` changed `current_contract_code` to return 2/3 on global-contract accounts). The
   `wasmbase-tool` executable still builds. Repair: restate the lemma for the new match arms.
