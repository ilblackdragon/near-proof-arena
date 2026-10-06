# D3 strategy: formal semantics and proving for NEAR WASM execution

Status: research, D3 checkpoint 1 (`docs/requirements/D3_WASM_REQUIREMENTS.md` §5.1). Lane `lane/v3-d3`,
2026-10-06. **This is research-scale work.** The estimates below are honest ranges, not plans, and nothing
beyond the checkpoint-1 PoC has been built.

Inputs: `docs/research/near-wasm-boundary.md` (what nearcore executes, cited as B#/H#),
`docs/research/wasm-formal-survey.md` (prior art, cited as A#/B#/C#), `docs/zk-formal/DESIGN.md` (our L1–L7
stack), and the PoC `examples/d3-wasm-poc/` (§5).

---

## 1. What has to be specified (requirements §2.1)

The trusted object is `exec : PreparedContract → VMContext → External → VMOutcome`, restricted to the PV86
behaviour described in the boundary doc. It splits into four layers. Each one has a separate evidence path:

| Layer | Content | Size class | Evidence |
|---|---|---|---|
| **W1 `Wasm.Decode/Validate`** | WASM 2.0 binary decoder + validator for NEAR's feature set (B4); limits (boundary §3.2); outcome of rejection (boundary §2.3) | 3–5k LOC | T vs nearcore prepare (accept/reject + error), T vs WasmCert/reference interpreter on the spec test suite restricted to B4; P: decoder totality, round trip where `Rel` needs it |
| **W2 `Wasm.Prepare`** | finite-wasm 0.6.1 gas analysis + max-stack analysis + NEAR prologue (boundary §3.3), as **tables attached to the original module**, not as rewritten bytes | 1–2k LOC | T vs nearcore (gas to the unit); P (stretch): `metering_equiv` (§3.3) |
| **W3 `Wasm.Exec`** | small-step machine over a *flat* operator array with precomputed control targets: i32/i64 ints, f32/f64 IEEE with canonical NaN (B3), sign-ext, sat-trunc, ref types, bulk memory, 1 table, `call_indirect`, globals, 64→128 MiB memory, stack budget, gas global + Wasmtime hook semantics (boundary §4) | 6–10k LOC | T vs nearcore per opcode and at scale; T→P vs a structured WASM semantics (SpecTec-generated or WasmCert-ported) |
| **W4 `Near.Host`** | 89 host functions (boundary App. A) incl. registers, promises/receipts, yield/resume, storage (+ recorded-storage counter, H8), logs; crypto primitives to their standards | 8–12k LOC + crypto specs 10–20k LOC | T (standard + Wycheproof vectors; nearcore difftest with adversarial arguments); shared ed25519/SHA-256 with D1/L5 |

Totality and determinism (requirements §2.1, class **P**) hold by construction: every definition is a
structurally recursive function, and execution takes an explicit step budget derived from `prepaid_gas`
(the PoC uses `fuel`). That leaves one lemma to prove: "the budget is never the binding constraint", i.e.
every step either charges at least one operator's gas within a bounded number of steps or terminates.

### 1.1 Reuse of existing formal WASM semantics (survey A1–A5)

No existing artefact is simultaneously Lean 4, executable, covering B4, permissively licensed and
maintained:
* WasmCert-Coq / WasmRef-Isabelle are the best *oracles* (their verified interpreters run the spec tests),
  but they are in other provers.
* SpecTec's Lean backend is an unmerged WIP that does not compile.
* Talos (Lean 4.34.1, the most complete) is AGPL-3.0, which blocks vendoring it into the trusted tree.
* linobit wasm-lean is MIT and has the right shape (interpreter proved sound against a relational
  semantics), but it is WASM 1.0, has phantom floats and is dormant.

**Decision: write our own W1–W3** in `spec/lean/v3/NearSpecV3/Wasm/*`, Mathlib-free and kernel-reducible
in the style of `F64.lean`. Use them as follows:
* three-way difftest: nearcore, our Lean, and an *independent* implementation for requirements §2.2
  (WasmCert-Coq's extracted interpreter or the OCaml reference interpreter for pure WASM, plus independently
  written host code);
* if SpecTec→Lean matures, prove per-instruction agreement for the B4 fragment. That is the realistic route
  to upgrading "faithful to the WASM spec" from T to P.

### 1.2 Floats

Floats are enabled and deterministic (B3), so `InD3` cannot exclude them silently. Three options:
1. **Specify them fully.** Exact-rational rounding as in `F64.lean`, extended to subnormals, ±∞, NaN and
   canonical NaN; f32 as a second instance; `min`/`max`/`nearest`/`trunc`/`sqrt` (sqrt by exact integer
   square root plus a sticky bit); conversions; sat-trunc. Roughly 2–4k LOC of spec. In the AIR this is the
   costliest chip family (§3).
2. **A staged `InD3α` that rejects modules containing float opcodes**, decidable at preparation time.
   This needs the lead's sign-off because it is a domain change. Mainnet Rust contracts rarely use floats,
   but some do (for example through `serde_json`), so this is a coverage cut, not a free one.
3. Both: (2) first, (1) as D3β.

Recommendation: (3).

## 2. Proving strategy: the options

Under our stack the AIR is **fixed per challenge** and defined in Lean (DESIGN §5.1). A per-contract
specialised circuit is impossible. Any approach must therefore be a *universal machine* AIR that reads the
program as committed data. The three options in the brief reduce to two real ones.

### (b) Compile to RISC-V, prove with a zkVM AIR: **rejected**
* It needs a proved WASM→RISC-V compiler (requirements §2.3.1 make it inadmissible otherwise). None exists
  (survey B6). Winch and Cranelift are unverified, and VeriISLE/Crocus/Arrival verify individual lowering
  rules, not the compiler. A CompCert-grade WASM→RV32 proof including NEAR's metering semantics is larger
  than everything else in this document.
* The variant "run an interpreter (wasmi) inside a RISC-V zkVM" needs a proof that the interpreter's RISC-V
  binary implements W3. That is the same compiler-correctness problem, plus ~17–22 RISC-V cycles per WASM
  instruction (survey C, SP1 measurements). Use it only as a cost baseline.
* We also have no admitted RISC-V AIR. SP1/OpenVM proofs are not in our L1–L4 stack.

### (a) / (c) A universal NEAR-WASM machine AIR with memory checking: **recommended**
(a) "an interpreter as an AIR" (zkWasm-style) and (c) "a direct WASM-execution AIR with permutation-based
memory checking" are the same design under our constraints. Both are a fixed CPU-like table that executes
one operator per row, looks the operator up in a committed code table, and keeps all mutable state in
offline-memory-checked RAM. The recommendation fixes the remaining design choices:

1. **Execute a flat prepared IR, not structured WASM.** The W2 output already gives, per operator, the
   jump target, the gas fee and (from validation) the static operand-stack height. A `br` then becomes
   "pc := target, sp := fp + h_static + arity, move `arity` values": there is no label stack at runtime.
   This is exactly the PoC's `endOf`/`elseOf`/gas tables. The translation "structured → flat" is part of the
   *spec* (a Lean function), so no unverified translator sits in the TCB. This closes the gap that zkWasm,
   rWasm and wasmi-in-zkVM all leave open (survey D.3).
2. **Charge gas per instruction in the AIR** and justify it by a Lean lemma `metering_equiv`. Block-level
   finite-wasm metering and instruction-level metering produce the same `burnt_gas`, `used_gas`, return data,
   logs, effects and failure bit. They may differ only in the error variant (`GasExceeded` vs
   `GasLimitExceeded`), and that variant is not consensus-observable (B10, H6). The PoC's ablation
   tests exactly this claim (§5). If `Rel` must keep exact error variants, the AIR instead commits to the
   W2 point table, which costs one extra column.
3. **Memory consistency:** one RAM argument with address spaces {operand stack, locals/frames, linear memory,
   globals, table, registers}. Accesses are (space, addr, time, value) tuples. A grand-product permutation
   (our L3/L4 bus, not LogUp, DESIGN §0) relates them to an address-then-time sorted copy, with continuity
   and read-after-write constraints and range checks on deltas. Linear memory is byte-addressed with up to
   8 bytes per access, or uses an aligned-word layout with a split decomposition. That is a budget decision
   for checkpoint 5.
4. **Numerics by lookups:** 16-bit limbs over BabyBear for i32/i64 (add/sub with carries, mul with range
   checks, div/rem by multiplication plus remainder bound), byte tables for and/or/xor/clz/ctz/popcnt, and
   shifts via powers-of-two lookups. Floats get a dedicated soft-float chip (D3β).
5. **Host calls** go over a bus to per-function chips:
   * memory reads/writes use the same RAM argument;
   * storage goes to the **L6 trie bus**, and sha256 to the **L5 digest bus**;
   * receipts, promises and logs go to the v3 runtime tables;
   * crypto chips are new: keccak-f[1600], ripemd160, and non-native curve arithmetic for ed25519 (shared with
     D1), secp256k1 ecrecover, p256, alt_bn128 add/mul/pairing, and BLS12-381 (including the PV86
     `not_in_group` behaviour, H7).
6. **Contract preparation as its own AIR.** Code bytes arrive from the trie (L6) and are hash-bound (L5).
   A decode/validate machine (the W1/W2 passes run as a trace) produces the code table on a bus keyed by
   code hash. Rejection is the same machine's trace ending in its first failing step, which is how
   `PrepareError`'s 0-gas outcome (B11) is proven without "proving a negative". The cost is per *distinct*
   contract per proof (up to 4 MiB of bytes), not per call.

### 2.1 Proof-obligation breakdown (composes with L1–L4, L5, L6)

Let `nearWasmAir` add tables CODE, PREP, EXEC, RAM, ALU, FLOAT, CALL, HOST_*, CRYPTO_* to the v3 AIR.

| Obligation | Statement (informal) | Class | Reuses |
|---|---|---|---|
| O1 PREP sound | `Holds` ⇒ for each code hash on the CODE bus, `CODE = flatten(prepare(bytes))` or the rejection outcome, where `sha256 bytes = code_hash` and `bytes` is the trie value | P | L5 digest bus, L6 trie bus |
| O2 EXEC step | per opcode family: row constraints + CODE lookup + RAM values ⇒ `Wasm.Exec.step` relates consecutive machine states | P | L4 `Expr.eval` lemmas |
| O3 RAM | permutation + sorted continuity ⇒ every read returns the latest write (generic, proved once, instantiated per address space) | P | L3 grand product, L4 bus semantics |
| O4 ALU / FLOAT | lookup rows ⇒ `binop`/`unop`/`relop` and IEEE ops equal the W3 definitions | P | — |
| O5 gas | gas column arithmetic in range, `metering_equiv` (W2 ≡ per-instruction on observables), outcome clamp | P | — |
| O6 CALL / stack budget | frames, the 262,144 budget, `MemoryAccessViolation` on exhaustion (B7) | P | O3 |
| O7 HOST | each host chip ⇒ the W4 spec of that function, including gas and errors | P (crypto: P against our spec; spec vs standard is T) | L5, L6, D1 ed25519 |
| O8 composition | `Holds nearWasmAir (publicOf c) tr → ∃ w, Rel_D3 c w` | P | L6 composition pattern |
| O9 completeness | honest trace from any `Rel_D3` instance within `Small` bounds, heights within `maxLog` | P | — |
| O10 side conditions | `Air.wf`, width/fingerprint budget, `NpOk` | P (`decide`) | L3/L4 |

### 2.2 Succinctness: the binding constraint is trace height, not width

* The chunk gas limit is 10^15 and `regular_op_cost` is 822,756, so one chunk can execute up to
  **≈1.2·10^9 WASM operators**.
* With the current np-udr-stark parameters (LDE ≤ 2^26 at rate 1/16, so tables ≤ 2^22 rows, DESIGN §4/§8)
  and ~1 EXEC row + 2–3 RAM rows per operator, one proof holds roughly **1–4·10^6 operators ≈ 1–3 Tgas of
  pure WASM**.
* Ordinary mainnet function calls burn 5–300 Tgas.
* Therefore **D3 at mainnet scale needs segmentation (continuations) plus aggregation/recursion**, proven
  inside our formal stack. Today the stack has neither. This is the largest structural gap, and it belongs on
  the requirements contract (§6 below).
* Prover time is a second gap. zkWasm's published steady state is ≈32k WASM instructions/s on an RTX 4090
  with KZG (survey C). Our CPU STARK with 512-bit hashing will be in the same order or slower, which is
  10^4–10^5 s per worst-case chunk against a 600 s cap. A D3 challenge therefore needs either an `InD3`
  per-chunk WASM-gas cap (honest workload classes) or very different hardware and caps.

### 2.3 Effort (honest, research-scale)

Lean LOC are calibrated against DESIGN §0 (70–105k for the v1 stack) and CertiK's zkwasm-fv (46.7k Coq
LOC, with lookups, ranges and allocator *axiomatised*, which we may not do).

| Work package | Lean LOC | Rust LOC | Calendar (1–2 dedicated lanes) |
|---|---|---|---|
| W1–W3 semantics (ints, floats, tables, bulk memory) + per-opcode difftest | 12–20k | 2–4k | 2–4 months |
| W4 host functions (non-crypto) + runtime integration (`RuntimeD3`) + scale difftest | 10–15k | 4–8k (oracle/v3 D3 traffic) | 3–5 months |
| Crypto specs (keccak, ripemd, secp256k1, p256, bn254 pairing, BLS12-381 incl. map-to-curve) + vectors | 10–20k | 1–2k | 2–4 months (parallel) |
| Core machine AIR (PREP, EXEC, RAM, ALU, CALL, gas): defs + O1–O6, O8–O10 | 60–120k | 15–25k | 9–18 months |
| FLOAT chip + O4 for IEEE | 15–30k | 3–5k | 3–6 months |
| Crypto chips, non-native EC + pairings (O7) | 20–60k **each** for pairing-capable curves | 5–10k each | 6–12 months each |
| Segmentation + recursion/aggregation inside the admitted stack | unknown (no prior art in our stack) | — | research |

**Total: roughly 150–300k LOC of Mathlib-free Lean, and multiple person-years.** Full D3, including pairings
and mainnet-scale gas, is not achievable on the timescale of the other v3 rungs. A *useful* staged D3 is:
* **D3α**: integer-only contracts, no curve host functions, per-chunk WASM gas ≤ the single-proof capacity;
* **D3β**: + floats;
* **D3γ**: + keccak/ripemd/secp256k1/ed25519/p256;
* **D3δ**: + bn254/BLS12-381 pairings;
* **D3∞**: + segmentation for mainnet-scale gas.

The re-execution reference candidate (`decide Rel_D3`, requirements §3.3) is much cheaper: W1–W4 plus
`RuntimeD3`. It is the realistic first ADMITTED D3 artefact, roughly 6–9 months.

## 3. What the PoC de-risks (and what it does not)

De-risked:
* finite-wasm's gas analysis and NEAR's prologue/hook semantics can be specified *on the original module*,
  without modelling instrumented bytes or wide arithmetic (B5);
* the flat-IR execution shape of §2(1) works;
* block-level vs instruction-level metering differ only in the error variant (§5);
* the nearcore oracle harness for single calls works against the pinned crate, with no TestEnv needed.

Not de-risked:
* floats, tables, `call_indirect`, bulk memory, globals, 87 of 89 host functions, promises, storage;
* every AIR question.

## 4. Recommendation

1. Adopt **(a)/(c): a universal NEAR-WASM machine AIR over a flat prepared IR**, with:
   * RAM consistency by a grand-product permutation;
   * per-instruction gas justified by a proved `metering_equiv`;
   * contract preparation as its own AIR on the L5/L6 buses;
   * host chips on buses.
   Reject (b).
2. Specify W1–W4 ourselves in `NearSpecV3.Wasm.*` and test three ways (nearcore, Lean, independent
   reference) at the requirements' 100k-call scale.
3. Sequence: re-execution reference first (checkpoints 2–4), then the AIR from D3α upward. Do the
   **segmentation/recursion design review before committing to AIR tables**, because it decides the table shapes.
4. Raise with the lead: the staged domain split, the per-chunk WASM-gas cap, and whether `Rel_D3` may
   quotient error variants (B10).

## 5. PoC results (examples/d3-wasm-poc)

See `examples/d3-wasm-poc/README.md` for the subset, the commands and the run log. Summary:
* **Differential test.** For each case, nearcore 2.13.4 (`near_vm_runner::prepare` + `run`, PV86 mainnet
  config, Wasmtime/Winch) and the Lean semantics both read the **same module bytes**. The test compares the
  full outcome line: status, burnt gas, used gas, and the exact return bytes or exact `FunctionCallError`.
* **Ablation.** The same Lean semantics was rerun with finite-wasm's cross-instruction merging disabled,
  i.e. instruction-level metering. It disagrees with nearcore only on the `window` family, and only in the
  error variant (`GasLimitExceeded` vs `GasExceeded`), never in gas. This is the empirical basis for
  `metering_equiv` (§2(2)).
