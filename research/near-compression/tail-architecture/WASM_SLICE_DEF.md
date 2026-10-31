# Bounded Wasm slice for the LaBRADOR vertical slice — NPMWASM01

2026-10-28. The pinned instruction set for the in-circuit Wasm VM vertical
slice on the LaBRADOR/NPMULT03 PQ backend. Tooling reused from the wasm-base
lane (`programs/gen.py`, `wasmasm.py`, `refinterp.py` — the spec-derived
interpreter is the independent correctness oracle); its SWIRL/WHIR backend
is NOT used (their 350–500 KB proofs are the comparison number to beat).

## Instructions in the slice

Core (all as i32 AND i64 forms, except where noted):
`const`, `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `shr_u`, `shr_s`,
`rotl`, `rotr`, `eq`, `ne`, `lt_s`, `lt_u`, `gt_s`, `gt_u`, `le_s`, `le_u`,
`ge_s`, `ge_u`, `eqz`; `div_s/div_u/rem_s/rem_u` are IN the slice for the
interpreter/KAT corpus but the FIRST circuit rung defers them (long div in
this frontend = shift-subtract chains; a stated, measured follow-up, not a
silent omission — the KAT corpus keeps div programs and they are excluded
from rung fixtures until implemented).

Locals: `local.get/set/tee` — fixed array of 16 (KAT programs use ≤ 4).
Globals: `global.get/set` — fixed array of 8 (KAT programs use ≤ 2).
Stack: `drop`, `select` — fixed depth 64 (KAT peak observed ≤ 8).
Control: `block`, `loop`, `br`, `br_if`, `return`, `end`, `if/else` — the
circuit form is generator-emitted bounded trips: the slice's KAT generator
emits programs with fixed loop trip counts, and the trace fixture carries
the flattened step sequence (honest bound, stated per fixture).
Calls: single-function programs only for the vertical slice (the `call`
KAT programs stay in the corpus for the follow-up rung).
Memory: `i32.load/store`, `i64.load/store`, `i32.load8_u/store8`,
`i64.load32_u/store32` — fixed 256-word (1024-byte) memory, byte-granular
little-endian like the interpreter; base+offset addressing with the same
natural-alignment immediates as wasmasm.py.

## Bounds (explicit, per fixture; not universal NEAR claims)

| Resource | Circuit bound | Corpus max |
|---|---|---|
| Steps | 2,048 | ladder rung |
| Stack depth | 64 | 8 |
| Locals | 16 | 4 |
| Globals | 8 | 2 |
| Memory | 1,024 B | 512 B |
| Bytecode | 16,384 B | 8,192 B |

## Gas

Per-opcode gas = 1 for the vertical slice (the wasm-base F1 diagnostic
profile); the fixture carries the expected total; the circuit sums it.
Real NEAR gas tables are a follow-up, not this slice.

## Trust boundary

The Python interpreter (`refinterp.py`, written from the WebAssembly 2.0
spec, sharing no code with any prover) is the HOST ORACLE: it defines the
expected step-exact traces that the CIRCUIT must reproduce. The circuit's
constraint sets are the PROVER side; the host audit (`audit_wasm_trace.py`)
re-executes every fixture against the oracle and requires step-exact
agreement, plus rejects a mutation battery. Neither side trusts the other;
the fixture format (NPMWASM01) is the shared contract. This slice is not
full NEAR validity: no host functions (the hostctx/storage KAT programs are
excluded from rung fixtures), no general control flow, bounded memory.
