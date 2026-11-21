# Lane A milestone A-T1: T1's Wasm call end to end

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §4.2 (M10), tracker `docs/zk-formal/E2E-T1-CRITICAL-PATH.md`.
Labels: **[M]** measured, **[K]** kernel-checked Lean (standard axioms, no `sorry`), **[S]** stated / design.

T1 = `/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3`: one FunctionCall to `d3tiny`
(code `8152bed2…`, 345 B), method `run`, input `again`, 26 Wasm steps, six host calls:
`input`, `register_len`, `read_register`, `storage_write` (existing key), `log_utf8`, `value_return`.

## 0. T1's call segments pre-check and prove at lane A's head [M] (2026-11-21)

Lane I reported that T1's only call could not be cut into segments on `wasmBaseSegAirMP` at any cut
size: the `storage_write` value group went on HOSTB under wire id `hid + 256 = 314`, and the HOST
row offers its bus-214 call key with `hid = 58` only. This is the bus-214 multi-group bug that
lane A's M6 fix FIX214 (`m6/README.md` §5.5) removed: `HOSTB.hid` is the base id, the group index
is the bits `hg0, hg1`, and the bus-210 wire id is `hid + 256·hg0 + 512·hg1`. Lane I's run used a
base or a `wasmbase-tool` / prover binary from before FIX214.

At main `7acdc7b82` (includes FIX214), with a fresh `wasmbase-tool` and a fresh release prover:

* `segcheck` at every cut size `K = 1 … 26`: **26/26 pass**. Every segment pre-checks (every
  constraint on every row, every bus balanced including bus 214 and the SHA-512 chip interface),
  and the boundaries chain (`logs/t1-segcheck-k1-26.txt`).
* `segprove` at `K = 8` (4 segments): 1,320,569–1,339,059 B, prove 15.6–30.0 s, verify 46–55 ms,
  statement ok (boundary public values, `code_root`, `func_root`), peak RSS ≈ 1.3 GB
  (`logs/t1-segprove-k8.txt`).
* `segprove` at `K = 26` (1 segment): 1,332,633 B, 25.5 s, verify 49 ms (`logs/t1-segprove-k26.txt`).
* Lane I's driver `t1/run_t1.sh` (`PROVE=1`, `STEPS=13`) with these binaries
  (`WASMBASE_TOOL`, `WB_PROVER`): "Wasm segments (wasmBaseSegAirMP) **pass** — 2 seg, precheck 2,
  chained True"; whole call proved and verified (`logs/t1-harness-k13.txt`).

Reproduce: `sweep.sh`, `harness.sh` (paths in `/data/illia/nearproof-deps/e2e-laneA/at1/env.sh`).
**Rebuild both binaries from the current tree**: the prover (`native/wasm-base`, `cargo build
--release`) and `lake build wasmbase-tool`. The AIR JSON comes from the Lean tool, so a stale tool
exports the pre-FIX214 HOSTB (no `hg0`/`hg1`) and reproduces exactly the reported failure.
