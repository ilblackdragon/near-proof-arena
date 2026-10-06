# oracle/wasm-d3: D3 WASM differential testing against pinned nearcore

* `src/main.rs` (crate `near-wasm-d3-harness`): runs pinned nearcore 2.13.4 `near_vm_runner::prepare` +
  `run` with the PV86 mainnet config (asserts `vm_kind == Wasmtime`; Winch on x86_64), a `MockedExternal`,
  no compiled-contract cache, account `alice.near`, balance 10^24. Input lines:
  `<prepaid> <wasm_hex> [<receiver>,…]` (optional output data receivers). Output:
  `ok <burnt> <used> <ret_hex|-> <balance>` or `abort <burnt> <used> <FunctionCallError Debug>`. Mode
  `prepare` prints the instrumented module (hex) or `prepare-error <variant>`.
* `lean/` (Lake package `WasmD3Driver`): the driver `nearspec-v3-wasm` for the D3α specification
  `spec/lean/v3/NearSpecV3/Wasm/*`. It prints the same line format. `--prepared-size` prints the exact
  instrumented size; `--instruction-level-metering` runs the metering ablation. It is a separate package so
  that the pinned `spec/lean/v3/lakefile.toml` is not modified.
* `tests/`: case generators and `difftest.py` (see its docstring). Families:
  * `opcodes`: per-opcode edge values, loads/stores, bulk memory, tables/refs/`call_indirect`, globals,
    start function, params/results, link and method-resolution paths, every NEAR preparation limit at the
    limit and one past it, the 16 MiB instrumented-size boundary, Wasmtime's 50,000-locals re-validation;
  * `random`: random well-typed D3α contracts;
  * `mutate`: byte-level mutants (decode/validate agreement);
  * `promise`: promise creation followed by out-of-gas inside a range (review F1), promise host errors, and
    data receivers;
  * `sizes`: exact instrumented size vs nearcore's `prepare_contract` output.

Build and run (shared host rules: `heavy` + `taskset`; no sccache for nearcore):

```sh
oracle/scripts/link-nearcore.sh
cd oracle/wasm-d3 && RUSTC_WRAPPER= CARGO_TARGET_DIR=/data/illia/nearproof-deps/target-wasm-d3 \
  taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy cargo build --release --locked -j 16
cd lean && taskset -c 8-15,24-31 lake build
cd ../tests && taskset -c 8-15,24-31 python3 difftest.py opcodes
taskset -c 8-15,24-31 python3 difftest.py random 5000 1
```
