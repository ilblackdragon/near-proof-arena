# In-circuit Wasm execution on the NEAR custom-circuit PQ path

2026-10-30. Status: **vertical slice proven and integrated** — a real Wasm
function's execution trace is expressed as explicit AND-constraints on the
LaBRADOR/NPMULT03 backend, KAT-accepted bit-exact against the spec-derived
interpreter, mutation-rejected in-circuit, measured on a ladder, and wired
into the receipt composite as **NPMULT04** (proven: 250,226 B packet,
7.2 s prove / 2.1-2.5 s verify at high load, log 23).

## What is expressed

The bounded Wasm slice (WASM_SLICE_DEF.md): i32/i64 core ALU (const, add,
sub, mul, and/or/xor, shl/shr_s/shr_u, rotl/rotr, eq/ne and the six signed/
unsigned comparisons, eqz), local get/set/tee, global get/set, drop/select,
bounded block/loop/br/br_if/return/end, and memory (i32/i64 load/store,
load8_u/store8, load32_u/store32) on a fixed 1024-byte memory.

The circuit (wasm_exec.rs, evidence/wasm-exec/phase4/) proves, per step:
the stack transition at the tracked height, local/global/memory updates,
the ALU result (a single shared 42-candidate chain selected by tag), gas,
and the entry/exit state — then asserts the public result, gas total, step
count, code digest, and init-state digest. The NPMULT04 composite proves
this section alongside the receipt lists, account trie, and ledger on the
same Session/commitment.

## What is bounded (stated, not silent)

| Resource | Bound |
|---|---|
| Steps | 2,048 (the frontend dense-build wall; the composite's Wasm section is capped per run) |
| Stack / locals / globals | 64 / 16 / 8 slots |
| Memory | 1,024 B (128 words), natural 8/4/1-byte alignment per op |
| Code | 16,384 B |
| Functions | single function; calls excluded |
| Control | generator-unrolled fixed trips; label arity 0/1 |
| Arithmetic | no div/rem in-circuit (corpus keeps them; deferred rung); no IntMul channel — mul is a shift-add ladder |
| Host calls | excluded |

## Trust boundary

- `refinterp.py` (spec-derived, sharing no prover code) is the HOST ORACLE.
  The tracing variant (wasm_trace_export.py) emits NPMWASM02 fixtures; the
  host audit requires byte-identical regeneration and rejects a 15-class
  mutation battery (195 mutants, including tag↔code-byte checks).
- The circuit is the PROVER side: it constrains the trace's semantics and
  binds the committed code (tight_sha256 == public digest) and init state
  (tight_sha256 == public digest). The statement is `n_steps, gas, result,
  code_len, code_digest[4], init_digest[4]`.
- **Named follow-up (code-walk rung)**: the per-step opcode-byte read
  (tag ↔ code[code_off]) and the label-table walk (branch targets) are
  host-audited only in this slice; the circuit trusts the fixture's step
  order and branch metadata (br_h/br_ar constrain the MOVE, not the label
  tree). Without it, a fabricated trace can rearrange instructions of the
  committed code; with it, the instruction sequence is fully bound.
- Not claimed: full NEAR validity, composed PQ security, recursive history,
  zero knowledge, or any 1-Pgas deadline.

## Measured (WASM_LADDER.md; high-load label, two observations)

- ~1,452 AND/step at the 2,048-step bound (2.99M AND) vs D0a's 4,792
  AND/slot (0.30x) — the slice is UNDER the relation's per-slot cost.
- Ladder: prove 0.26/0.33/0.70/2.01-2.03 s and verify 0.13/0.17/0.31/0.65 s
  for 8/64/512/2048 steps; packets FLAT 157-209 KB (vs the 350-500 KB
  SWIRL/WHIR baseline); RSS 532-6,288 MB.
- Suite boundary measured: rungs land on logs 18/20/22 (sizes/sizem/sizel);
  log 23-24 selects sizexl (moduli swap Q4861→Q9721) — the composite
  stays at log 23, so no crossing occurred.
- Composite NPMULT04: 250,226 B (+100 B over NPMULT03's 250,126 B — the
  recursive opening dominates), prove 7.2 s, verify 2.1-2.5 s, RSS 13.25 GB,
  AND 4,402,980 = receipt 4,191,295 + Wasm 211,685; all receipt negative
  checks (112 table mutations, root mutation, digest mutation) still reject.
- 1-Pgas extrapolation (labeled EXTRAPOLATION): ~1.5-8.7 GAND per chunk
  (~500-2,900x the largest rung) — folding/per-block composition is
  required; the 300 KB packet target survives (flat bytes); single-circuit
  CPU proving cannot reach 1-2 s (GPU opening + folded per-block verify
  remain the levers); the 2,048-step dense-build wall breaks first.

## Decision

By the goal's measured rule the slice was **integrated** (1,452 < 4,792
AND/slot): NPMULT04 proves the Wasm section with the receipt composite at
essentially the NPMULT03 packet size. Open: code-walk rung, div/host calls,
GPU opening, folded per-block verify, 1-Pgas composition.
