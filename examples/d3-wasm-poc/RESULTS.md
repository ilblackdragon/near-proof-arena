# D3 PoC difftest run log

Both sides read identical module bytes. The comparison covers the full outcome line: status, burnt gas,
used gas, and the exact return bytes or the exact `FunctionCallError` Debug string. nearcore side:
`oracle/wasm-d3` linked against nearcore 2.13.4 `44f7ae6` with the PV86 mainnet config (Wasmtime, Winch,
x86_64). Lean side: `lean/` (`WasmPoC`, Lean 4.34.1). Host: shared box, `taskset -c 8-15,24-31`.

## 2026-10-06: final generator (window family targeted at the basic-block window)

| Seed | Cases (random / window / recursion) | Disagreements | nearcore time | Lean time (8 shards) |
|---|---|---|---|---|
| 1 | 2000 (1800 / 122 / 78) | **0** | 1.5 s | 118.6 s |
| 2 | 3000 (2680 / 173 / 147) | **0** | 3.7 s | 182.9 s |
| 3 | 2000 (1788 / 126 / 86) | **0** | 2.7 s | 219.5 s |
| **Total** | **7000** | **0** | | |

Outcome classes (seed 2):

| Outcome | Count |
|---|---|
| ok | 1015 |
| `HostError(GasExceeded)` | 771 |
| `WasmTrap(MemoryOutOfBounds)` | 405 |
| `WasmTrap(IllegalArithmetic)` | 244 |
| `CompilationError(PrepareError(Deserialization))`, 0 gas | 185 |
| `HostError(GasLimitExceeded)` | 142 |
| `HostError(MemoryAccessViolation)` (stack budget and host out-of-bounds) | 124 |
| `HostError(GuestPanic)` | 60 |
| `WasmTrap(Unreachable)` | 31 |
| `HostError(InvalidRegisterId)` | 18 |
| `HostError(IntegerOverflow)` | 3 |
| `HostError(ReturnedValueLengthExceeded)` | 2 |

Seeds 1–2 ran on the build before `--instruction-level-metering` was added; that flag's default is the
unchanged semantics. Seed 3 ran on the committed build.

## Ablation: instruction-level metering (`D3_LEAN_ARGS=--instruction-level-metering`)

This flag disables finite-wasm's cross-instruction merging (`Prepare.optimize`), so every operator is
charged on its own.

| Seed | Raw disagreements | With `D3_QUOTIENT_GAS_ERRORS=1` |
|---|---|---|
| 1 | 50, all in the window family, all nearcore `GasLimitExceeded` vs ablation `GasExceeded`, identical gas | **0** |
| 3 | 46, same pattern | **0** |

Reading:
1. The difftest is **sensitive** to the metering granularity. A semantics that charged per instruction would
   be caught.
2. On these 4000 **promise-free** cases, instruction-level metering agrees with nearcore on every
   consensus-observable field. This does **not** generalise: once a promise exists, an out-of-gas abort charges
   the whole finite-wasm range (review F1, `docs/reviews/D3_REVIEW_2026-10-06.md`), so `burnt_gas` differs. The
   `metering_equiv` lemma is retracted, and the AIR must commit to the finite-wasm point table.
3. `used_gas` equals `burnt_gas` in every case here (no promises), so that column carries no extra information
   (review F10). Seeds 1–2 ran on a build before the ablation flag existed; the flag's default is unchanged
   semantics (review F9).

## Earlier runs (superseded)

The first generator aimed the window family about 3,900 pages too high, so it never reached the
basic-block window. With that generator, seeds 1 (2000) and 2 (3000) also gave 0 disagreements, and the
ablation also gave 0. That exposed the targeting bug, which was fixed by solving for the page count from
the module's loading fee.
