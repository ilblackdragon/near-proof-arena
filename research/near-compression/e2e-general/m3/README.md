# E2E milestone M3: the chunk's own host tape

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §4 (M3) and §5. Date 2026-11-03.
Labels: **[M]** measured here.

## What changed

Milestone 1 ran the Lean interpreter (`wasmbase-tool prepIf`) in the **default** host context. Its
host answers were therefore not the chunk's, and burnt gas differed: T2 by 11.4 Ggas
(5 × `read_cached_trie_node`), T1 by 28.1 Ggas (evicted `storage_write`).

`wasmbase-tape` (`wasm-base-lean/Tape.lean` + `tape_shim.c`, built by `build-tape.sh`) runs the
**unmodified** Lean checker `Schema.checkVersioned (Tier.cfg .allFeatures)` on a case, exactly as
`nearspec-v3-check-successor --tier allFeatures` does, and records every Wasm call it makes.

How the calls are recorded:
* The checker's compiled `runCallWithLimitsFast` is wrapped at link time (`-Wl,--wrap`).
* The wrapper returns the real result **unchanged**, so verdicts are the checker's.
* It then replays the call with the spec's own `step`, from the checker's own `CallCtx` and
  trie-backed `RealStore` (accounting cache, recorder, overlay).
* For each host call it writes the answer: status, result word, `g_after` and register fills.

The output is a `prepIf`-format prep per call. The replay's final state is compared with the real
result (`replayMatches`).

`nearproof-wasm-base check-tape` builds the `wasmBaseIfRegAir` trace from each prep and runs the full
constraint and bus pre-check. It reads back two things:
* the trace's own final budget `g_final_trace` (each host call's `g_after` resynchronisation, plus `R`
  per charged unit since);
* the HOSTB payloads.

`sweep.py` compares these with the checker's outcome of that call:
* burnt gas: `preSync.burnt + preSync.remaining − g_final_trace`;
* logs: the `log_utf8` groups;
* return value: the last `value_return` group;
* status.

```sh
research/near-compression/wasm-base-lean/build-tape.sh
research/near-compression/e2e-general/m3/run.sh OUT /data/illia/nearproof-deps/corpora/d3c{7,8,9,10}/d3
```

## Results [M] (`logs/summary.json`, binaries in `logs/SHA256SUMS`)

The corpus run covers 19,007 cases (d3c7–d3c10). All are `accept`, the same verdict the unwrapped
checker gives. The checker made 27,197 Wasm calls, and the replay matches the real result on every
call that ran a method (0 mismatches).

| class | calls |
|---|---|
| the trace with the chunk's own answers equals the chunk's outcome (status, burnt gas, logs, return) | **3,414** |
| outside the current AIR's coverage (`checkModuleIfH`: `d3rich.run/cb`, `e1fe4f9c.run`, `3b1ad423.run`, `d3ed`) | 23,317 |
| no method run (preparation, loading, link or resolve outcome: no Wasm executed) | 466 |
| eligible but different, or trace generation failed | **0** |

| code | eligible calls, all equal |
|---|---|
| `d3tiny` (`8152bed2`) | **1,755 / 1,755** (`run` 1,751, `cb` 4) |
| `3b1ad423` | 1,293 (`cb`; its `run` is not eligible) |
| `d3rich` (`fbc015a8`) | 194 (`noop`) |
| `d3hostx` (`f1c929ab`) | 172 |

The plan quoted 1,685 `d3tiny` executions. This run counts 1,755 calls: every checker invocation of
the `d3tiny` code over d3c7–d3c10, including 4 `cb` calls.

| target | chunk burnt (Lean checker = clean-room) | trace with chunk tape | logs | return |
|---|---|---|---|---|
| T1 `d3c8/d3/02-h10196-s3` call 0 | 121,110,620,829 | **equal** | `tiny` equal | `again` equal |
| T2 `d3c9/d3/00-h10018-s0` call 0 | 104,421,422,859 | **equal** | `tiny` equal | `hello` equal |

T1's tape takes the evicted path: `storage_write` returns 1 and fills register 1 with the old value,
which the trace generator now models as a REG fill.

T1 with its chunk tape was proved and verified on the main stack: 1,476,278 B, 268.2-bit, prove
25.0 s, verify 50 ms, 8 threads.

## What the equality does and does not say

* It is an equality *outside* the proof.
* The trace is built from the chunk's own answers, and its gas, logs and return then equal the chunk's.
* Inside the proof the answers still come from the HOSTO oracle. A consistent change of HOST and HOSTO
  `g_after` still verifies (`../m1/logs/M1a-T2-call0-tamper.log`, `TAMPER-GAP`).
* Binding the answers is M6 (the state rows produce HOSTQ/HOSTR/HOSTB).
* One case is out of the trace generator's domain: a register **refilled** while live. It panics with
  a message rather than emitting an unsound trace, and it never occurs among the eligible calls.
