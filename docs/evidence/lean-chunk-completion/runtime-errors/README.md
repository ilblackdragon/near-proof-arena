# Runtime-error branches of the pinned runner (W03, UQ-014)

Target: nearcore 2.13.4 (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`), PV86, mainnet parameters.
Lean checker `nearspec-v3-check-successor` sha256 `b65fe05c…` (unchanged by this package). Generator:
`oracle/v3-successor` with the new opt-in `runtime-errors` scenario.

UQ-014 asked whether the `LoadingError`, `WasmUnknownError` and resource `LinkError` branches
(boundary hazards H2/H9/H10), together with execution-slot retry exhaustion, are really absent at
PV86. Each construction site in the pinned runner and runtime now has one of three dispositions:

* **(a)** unreachable for a validating node given the inputs, with a source argument;
* **(b)** reachable from chunk content: modelled in Lean, and checked against whole-chunk fixtures
  from pinned nearcore;
* **(c)** reachable only through host state (memory, mmap, the on-disk compiled-contract cache,
  thread concurrency). This is not a property of the chunk, and nearcore's validator treats any
  divergence it causes as a node-local witness failure.

No branch is left "assumed absent".

**Result:** 4 seeds, 33,930 whole-chunk verdict rows (814 honest chunks and 33,116 mutants).
0 Lean/nearcore disagreements and 0 out-of-domain verdicts. Blind replay: 814/814 honest chunks match
on all 11 header outputs. The deliberate-breakage checker (no loading check, every import links)
rejects 209 of the 814 honest chunks. Every `LinkError` chunk is detected. A `LoadingError` chunk
escapes detection only where the ablated outcome is consensus-identical (§3.3). No Lean change was
needed. One ordering theorem was added (§2). The 3,138-case census and the 577 fixtures did not
move (§4).

## 1. VM at PV86: Wasmtime

`core/parameters/res/runtime_configs/84.yaml:2` switches `vm_kind` from `NearVm` to `Wasmtime`.
`parameters.snap:243` records `vm_kind Wasmtime` for the PV86 snapshot. The runner dispatches on it
in `runtime/near-vm-runner/src/runner.rs:204-226`, and `wasmtime_vm` is the default feature
(`runtime/near-vm-runner/Cargo.toml:89`). Wasmtime 45.0.0 (`Cargo.lock`). It runs with Winch on
x86_64 (`wasmtime_runner/mod.rs:517-521`) and a pooling allocator sized for `MAX_CONCURRENCY = 1000`
instances (`mod.rs:47, 481-493`). The `near_vm_runner/` constructions are NearVm-only and are not
reached at PV86.

## 2. Dispositions, construction by construction

Paths are under `runtime/near-vm-runner/src/` unless stated. `W45` is
`~/.cargo/registry/.../wasmtime-45.0.0/src/`.

### 2.1 `LoadingError` (H9)

The only construction in the Wasmtime runner is `Module::deserialize(...).map_err(LoadingError)`
(`wasmtime_runner/mod.rs:744-745`). It sits inside the cache-lookup closure of
`with_compiled_and_loaded` (`:683-820`). `runtime/runtime/src/function_call.rs:328-330` turns it into
`VMOutcome::nop_outcome`: zero burnt and used gas, `aborted = LoadingError`
(`logic/logic.rs:4511-4524`). That is a failed `FunctionCall` action, so the receipt fails and its
deposit is refunded. It does not abort the chunk, and the outcome root stores only `Failure`. The
early `return` also skips `distribute_gas`.

`Module::deserialize` fails in these ways:

| cause | where | disposition |
|---|---|---|
| instance layout above the pool's 1 MiB `core_instance_size` | `W45/runtime/module.rs:548-551` → `vm/instance/allocator/pooling.rs:635-643, 422-476` | **(b) modelled**: `Wasm/InstanceLayout.lean` (`instanceAllocationFits`), `runCallWithLimits` with `loadingLimits` (`Wasm/Exec.lean:660-670`), on in every wide tier including `allFeatures` (`Successor/Config.lean:362`) |
| pooled memory count/size, shared memory | `pooling/memory_pool.rs:300-341` | **(a)**: after preparation a module has exactly one defined, unshared memory of 1,024..2,048 pages, whatever it declared (`prepare/prepare_v3.rs:126-141, 347-357`; memory imports rejected `:322`). The pool's limit is 2,048 pages (`mod.rs:474, 484`) |
| pooled table count / table minimum | `pooling/table_pool.rs:62-90` | **(a)**: preparation enforces `max_tables_per_contract = 1` and initial ≤ `max_elements_per_contract_table = 10,000` (`prepare_v3.rs:107-124`; table imports rejected `:320`; `82.yaml:12-13`), the same values as the pool (`mod.rs:474-492`) |
| artifact compatibility header / decode | `W45/engine.rs` `load_code_bytes`, `module.rs:414-416` | **(c)**: the artifact comes from this engine's `precompile_module` (`compile_uncached`, `mod.rs:567-597`), under a cache key that binds code hash, VM config hash, VM kind and the engine compatibility hash plus a version (`cache.rs:55-67`, `vm_hash` `mod.rs:555-563`). A mismatch means a foreign or corrupted cache entry, which is host state |
| mmap / mprotect / fallible allocation (`try_new`) | `W45/module.rs:528-533, 545` | **(c)** host resources |

The instance-layout cause does not depend on cache state. The cache stores the *compiled* artifact
(`CompiledContract::Code`, `compile_and_persist`, `mod.rs:654-675`), and the allocator check runs again on every
deserialization. So a cold node, a warm node and a node that compiled the code at deploy time
(`runtime/runtime/src/actions.rs:335` → `cache_warming.rs:77`, result ignored) all reach the same `LoadingError`. The
fixtures cover each path: genesis code, which the generator precompiles into every client's cache;
code deployed in the same receipt; and code deployed in an earlier chunk. The cold validator judges
every case. A compilation error is cached as `CompileModuleError` and returned as
`CompilationError` (`mod.rs:706-717`). It is never a `LoadingError`.

**Order.** Deserialization (`:744`) runs before the loading fee (`:797-808`), before
`instantiate_pre` (`:757`) and before method resolution (`prepare`, `:874-905`). Lean has the same
order. `runCallWithLimits` checks the layout before `runCall` charges, links or resolves anything.
The new theorem `Successor.runCallWithLimits_loading_precedes` (`Successor/TierMono.lean`) states that
an over-limit module gives the same zero-gas `LoadingError` line whatever the method, context
(prepaid gas, deposit) or fuel. Its axioms are `propext`, `Classical.choice` and `Quot.sound`. The
fixtures exercise all of these: over-limit modules called with a missing method, with 1 Mgas (below
the loading fee), and with an unknown import as well. nearcore gives `LoadingError` with zero gas in
every case, and Lean agrees.

The pinned harness confirms the layout boundary at the exact global count for three module shapes,
including imports, a table and escaped functions (`boundary.json`). This agrees with
`instanceAllocationBytes`: shape A (1 import, `main`) fits at 65,501 globals and not at 65,502;
shape B (5 imports, 31 exports, 40 `ref.func` elements, 1 table) at 65,344/65,345; shape C (no
imports) at 65,505/65,506. The chain fixtures use exactly these pairs.

The comment in `Wasm/InstanceLayout.lean` calls the memory "imported". Under Wasmtime, preparation
*defines* and exports it (`prepare_v3.rs:327, 347-368`). The 24-byte term is still correct (an
8-byte defined-memory pointer plus a 16-byte owned `VMMemoryDefinition`), so only the wording is
wrong. The file was left unchanged to avoid rebuilding the checker's closure for a comment.

### 2.2 `LinkError` (H2, H10)

| construction | where | disposition |
|---|---|---|
| unknown import / wrong import type at `instantiate_pre` | `mod.rs:757-765` → `into_vm_error` `:414-419` | **(b) modelled**: `Wasm/Prepare.lean` `link` + `HostSigs.lean` (89 PV86 production imports). The loading fee is charged first (`:797-808`), and the outcome is a failed call that burns the fee. Fixtures below |
| `memory export missing` | `mod.rs:746-753` | **(a)**: preparation always emits the `memory` export and drops any user memory export (`prepare_v3.rs:175, 193, 359-368`), and the cached artifact is always prepared code (`compile_uncached`, `mod.rs:567-570`) |
| `failed to acquire execution slot` (retry exhaustion) | `mod.rs:1012-1018`, `try_acquire` `:230-269` | **(c)**: `try_acquire` returns `None` only when the first reservation fails (more than 1,000 live instances in the process, `:208-218`) and then 65,535 retries fail (`u16` counter, `:241, 257`), or on a counter underflow. Each executing thread has at most one live instance (NEAR has no synchronous cross-contract calls), so the count is bounded by the node's thread pools (apply-chunk spawner limited to `3 · shard_limit`, `nearcore/src/lib.rs:313-315`), not by chunk content |
| other instantiation errors (pool slot, memory image mapping, mmap) | `mod.rs:1019-1026` → `:414-419` | **(c)**: the permit keeps live instances within the pool, and a full pool flushes the decommit queue and retries (`W45/vm/instance/allocator/pooling.rs:514-525`). `StoreLimits` cannot refuse a prepared module at instantiation: 1 instance, 1 memory of ≤ 128 MiB, ≤ 1 table of ≤ 10,000 elements (`mod.rs:333-339`); a failed `memory.grow` returns −1. What remains is OS resources |
| gas-hook burn failure | `mod.rs:1047-1061` (`burn_gas(...)?` is not wrapped in `ErrorContainer`) | **(a)** (H5): the hook burns at most `remaining_gas`, which exceeds the limit only past `max_gas_burnt`. Every prepaid gas is ≤ `max_total_prepaid_gas` (`runtime/runtime/src/action_validation.rs:117`), and contract-created receipts carry gas from a prepaid ≤ that bound. At PV86 both limits are 10¹⁵ (`parameters.snap:202, 212`). Lean reports it as `unmodeled` (`Wasm/Machine.lean:412-419`), never an accept |
| non-trap, non-container error from `start` / `main` | `mod.rs:1073-1082, 963-978` | **(a)**: host functions wrap every error in `ErrorContainer` (`mod.rs:1127-1155`). `func.typed` cannot fail after the `[] → []` check (`:887-905`). Wasm faults are traps (§2.3) |

Imports and preparation. Preparation does **not** validate imported function names or types
(`prepare_v3.rs:315`, "TODO: validate imported function types here"). It rejects only non-`env` modules
and non-function imports (`:310-323`). The fixtures confirm which error each case reaches:

* an unknown `env` function gives `LinkError` "unknown or invalid import". The names tested are
  `no_such_host`; `burn_gas` and `sleep_nanos`, which exist only with `test_features`
  (`imports.rs:377-384`); `sandbox_debug_log`, `sandbox` only (`:373`); and `finite_wasm_gas` under
  `env` (the instrumentation hook lives in module `internal`);
* a known name with a wrong signature gives `LinkError` with wasmtime's `types incompatible` text.
  The names tested are `storage_write`, `value_return`, `input`, `block_index`, `panic`,
  `promise_create` (7 instead of 8 parameters) and `read_register`;
* `foo.input` and `internal.finite_wasm_gas` give `CompilationError(PrepareError(Instantiate))`.
  Contracts therefore cannot reach the gas hook;
* table and global imports give `PrepareError(Instantiate)`, and a memory import gives
  `PrepareError(Memory)`.

The ExecutionError text differs from Lean's for a type mismatch. That does not matter, because the
outcome root hashes only `Failure` (B10).

### 2.3 `WasmUnknownError`

Two constructions, `wasmtime_runner/mod.rs:403-407` and `:409-412`, turned into a zero-gas failed
call by `function_call.rs:331-337`.

* **`C::Unknown` (a).** `TrapClassification::from` (`wasmtime_runner/trap_classification.rs:33-96`)
  names all 48 variants of wasmtime 45's `Trap` (`wasmtime-environ-45.0.0/src/trap_encoding.rs:66-227`):
  11 classified and 37 listed as `Unreachable`. The wildcard is therefore dead for this pinned
  wasmtime. nearcore's `test_all_wasmtime_traps_classified` (`:101-113`) enforces this.
* **`nondeterministic trap` (a).** `Interrupt` is raised only by the epoch-deadline libcall
  (`W45/runtime/vm/libcalls.rs:1271`). Epoch interruption is off by default (`W45/config.rs:733`), and
  nearcore never enables it or fuel (`wasmtime::Config::default()`, `features.rs:132-138`; no
  `epoch_interruption`/`consume_fuel` in `runtime/`). `HeapMisaligned` needs atomics, and
  preparation's validator rejects threads (`features.rs:9`).

The `Unreachable` arm (`mod.rs:396-401`) is not a `WasmUnknownError`. Its trap codes (GC, function
references, component model, fuel, threads, pulley) belong to proposals that preparation rejects
(`features.rs:7-24`). Lean names only the reachable `WasmTrap` kinds (`Wasm/Machine.lean:21-22, 170`).

### 2.4 Cache-state paths (`CacheError`)

The cache paths are `read_cache`/`cache.get`/`cache.has` (`mod.rs:141, 638, 705, 835`) and
`cache.put` (`:673`). They give `VMRunnerError::CacheError`, which `function_call.rs:322-327` turns
into `StorageInconsistentState`, a runtime error that aborts the chunk application. In witness
validation that `Err` propagates (`chain/chain/src/stateless_validation/chunk_validation.rs:605-614`),
and the validator logs it and sends no endorsement
(`chain/client/src/stateless_validation/chunk_validation_actor.rs:477-505`). **(c)**: this is a
node failure, not a verdict. A truncated or unknown-tag cache file is treated as a miss
(`cache.rs:820-848`). The deploy-time precompile ignores its result (`cache_warming.rs:77`).

**Named environment assumption (c).** Every (c) row reduces to one condition. The validating node's
process has the memory, address space and file system its configuration requires, and its
compiled-contract cache holds only entries that this engine wrote. `Rel_D3` and the successor
checker are deterministic functions of claim and witness. If the condition fails on a validator,
any outcome that differs from Lean's also differs from the chunk header. That validator then fails
`validate_chunk_with_chunk_extra_and_receipts_root` (`chunk_validation.rs:755`) and does not
endorse. If it fails on the producer, the honest validators and Lean both reject the chunk. So no
host condition turns a chunk that Lean rejects into one that nearcore accepts. It can only cost a
node its endorsement.

## 3. Whole-chunk fixtures from pinned nearcore

### 3.1 Scenario

`NEAR_SUCCESSOR_SCENARIO=runtime-errors` (`oracle/v3-successor/src/xfam.rs` `runtime_errors`,
contracts `src/rterr.rs`) is a quiet chain: no baseline traffic and no crafted injections. It runs
101 steps on 15 dedicated accounts across 4 shards (`steps.md`, from seed 601):

* direct calls to the three boundary pairs, an over-limit module (66,000 globals) and an
  over-limit module with an unknown import, plus `LinkError` modules;
* cross-shard calls, and `promise_then` chains from an `xfam` caller whose callback records the
  callee's status;
* missing methods, and gas below the loading fee;
* multi-action receipts (a transfer before a failing call, a call before a transfer, two calls);
* 24 contracts deployed in-chain three ways: deploy+call in one receipt (a failing call rolls the
  deploy back), deploy alone, then a cross-shard call.

The collector (`tools/d3/collect_xfam.py`) fails a run unless nearcore produced `LoadingError`,
`LinkError`, `PrepareError(Instantiate)` and `PrepareError(Memory)` receipts, every `fit` account ran
successfully, and every `over` account failed with `LoadingError`. All four runs pass. Without the
scenario, the generator output is byte-identical to `HEAD`: seed 7, 2 chains, 40 blocks,
`--mutate-every 10`, 8,545 files, `diff -r` empty.

```
bash oracle/scripts/link-nearcore.sh
CARGO_TARGET_DIR=/tmp/lean-global-oracle-target cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
for a in "601 0" "602 6" "603 12" "604 24"; do set -- $a
  NEAR_SUCCESSOR_SCENARIO=runtime-errors NEAR_XFAM_MUTATE_EVERY=1 near-arena-oracle-v3-successor gen --domain d3 \
    --seed $1 --first-chain $2 --chains 1 --blocks 90 --p-missing 0.1 --mutate-every 0 --code-mutant-p 0 \
    --ood-cap 100000 --drop-cap 12 --out re$1
  python3 tools/d3/collect_xfam.py --source re$1 --out col/re$1
  cat col/re$1/honest.txt col/re$1/mutants.txt > col/re$1/all.txt
  python3 tools/d3/replay_successor.py --tier allFeatures --cases-file col/re$1/all.txt --out col/re$1/rep-main --jobs 12 --batch 20
  python3 tools/mainnet-replay/blind_corpus.py --binary spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor \
    --cases col/re$1/honest.txt --root / --out col/re$1/blind --tier allFeatures
done
python3 tools/d3/summarize_runtime_errors.py --col col --runs re601 re602 re603 re604 --out summary.json --steps steps.md
```

### 3.2 Results

See `summary.json` for per-run partitions.

| seed (chain) | honest | mutants | verdict rows | disagreements | blind | ablation detected |
|---|---|---|---|---|---|---|
| 601 (0) | 208 | 8,407 | 8,615 | 0 | 208/208 | 53 / 208 |
| 602 (6) | 203 | 8,192 | 8,395 | 0 | 203/203 | 52 / 203 |
| 603 (12) | 199 | 8,183 | 8,382 | 0 | 199/199 | 52 / 199 |
| 604 (24) | 204 | 8,334 | 8,538 | 0 | 204/204 | 52 / 204 |

**Total: 814 honest + 33,116 mutants = 33,930 verdict rows, 0 disagreements, 0 out of domain; blind 814/814 match on all 11 header outputs (state, outcome and outgoing-receipt roots, gas, balance burnt, proposals, tx root, encoded root and length, congestion, bandwidth requests); 209/814 honest chunks detected by the ablated checker.** Over all rows, nearcore and Lean both accept 8,036 and both reject 25,894: 814 honest chunks, 7,222 mutants nearcore accepts (for example reordered or duplicated code blobs and unchecked fields) and 25,894 it rejects.

Every row is `verdict_compared_agree`: every case is in the `allFeatures` domain and has a nearcore
verdict. The receipts per run are nearcore's: 23–24 `LoadingError`, 33 `LinkError`, 8
`PrepareError(Instantiate)`, 2 `PrepareError(Memory)`, 2 `GasExceeded`, and 218 successes.

### 3.3 Deliberate-breakage control

`checker-ablate` (sha256 `24845662…`) is a temporary build of this tree, not committed, with `StorageExecution` calling
`runCall` instead of `runCallWithLimits` and with `link` returning `.ok`. It was run on the honest
chunks of every run:

| chunks applying a receipt of kind | detected | missed |
|---|---|---|
| `LinkError` | 127 | 0 |
| `LoadingError` | 82 | 4 (one per seed: `19.missing-method.s3rtovrc`) |
| `PrepareError(…)` (not ablated) | 0 | 40 |

Chunks can apply receipts of more than one kind, so the rows overlap; 209 distinct honest chunks are
detected in total.

An honest chunk is detected when the ablated checker rejects it. Each `LinkError` chunk is detected:
the module runs, and its storage access is missing from the witness or changes the state root.
Most `LoadingError` chunks are detected too. Those that escape apply only a missing-method call
into an over-limit module of shape C. Without the loading check, that call is a zero-gas
`MethodNotFound` failure, which is consensus-identical to the zero-gas `LoadingError`. The
preparation-error chunks are not ablated; those checks predate this package.

## 4. Census and fixture movement

The checker is unchanged: `b65fe05c…` before and after; the only Lean addition is a theorem in
`TierMono`, which is not in the checker's closure. Same populations, replayed before and after with
`tools/d3/replay_successor.py`:

| population | tier | before | after | moved |
|---|---|---|---|---|
| 3,138 gap census | `allFeatures` | 3,138 accept | 3,138 accept | 0 |
| 3,138 gap census | `signed` | 735 accept / 2,403 out of domain | same | 0 |
| 577 committed fixtures | `allFeatures` | 577/577 agree (402 accept, 175 reject) | same | 0 |

## 5. Files

* `summary.json`: per-run populations, verdict partitions, blind and ablation results, receipt
  kinds.
* `steps.md`: the 101 steps with nearcore's receipt kinds (seed 601).
* `boundary.json`: the harness boundary search (largest fitting global count per shape).
* `manifests/re60?.json.gz`: collector manifests (per step: receipts, statuses, gas, cases).
* `replay/rows-re60?.jsonl.gz`: per-case `allFeatures` verdict rows. `replay/ablate-re60?.jsonl.gz`:
  the ablated checker's rows. `replay/blind-re60?.json`: the blind reports.
* `cases.tar.gz` + `cases-index.json`: 10 honest chunks and 30 mutants of seed 601
  (`tools/d3/select_xfam_fixtures.py --honest 10 --mutants-per-case 3`). Replayed from the
  extracted files: 40/40 agree (10 accept, 30 reject).

## 6. Open

* The layout model is pinned to the x86_64 Winch build. An aarch64 Cranelift validator has the same
  `VMOffsets` (64-bit host pointers), but this was not measured.
* Disposition (c) rests on the named environment assumption (§2.4). It is a statement about node
  operation, not something a relation over claim and witness can check.
