# Segmentation and proof composition: requirements for the recursion research track

Status: requirements contract, v0.1 (2026-10-06). Drafted in lane `lane/v3-d3` at the lead's request.
**Changes to §§2–4 need the lead's sign-off.**

Parent: `docs/requirements/D3_WASM_REQUIREMENTS.md` v0.2, §2.5. This track decides whether uncapped,
mainnet-scale D3 is possible under the arena's admission theorem.

## 0. The problem

* A NEAR chunk may burn up to 10^15 gas. In pure WASM at `regular_op_cost` = 822,756 that is
  ≈1.2·10^9 operators.
* One np-udr-stark proof has tables ≤ 2^22 rows (LDE ≤ 2^26 at rate 1/16; `docs/zk-formal/DESIGN.md`
  §4/§8). That holds ≈1–3 Tgas of WASM (`docs/research/near-wasm-strategy.md` §2.2).
* Mainnet-scale D3 therefore needs **segmentation**: the execution is split into S ≈ 10^2–10^3
  segments, each proved over bounded tables.
* It also needs **composition**: one admitted artefact must establish `Rel_D3` for the whole chunk, under
  `AdmissionStatement` (`formal-core/ArenaCore/Admission.lean`), within the challenge's proof-size,
  verify-time and prove-time caps.

## 1. The obstacle: instantiating the random oracle inside a circuit

`CryptoSound`'s random-oracle branch (`Admission.lean:105-118`) needs three things. First, an honest
prover complete **for every** hash function `H`. Second, `RomSound` (`Security/ROM.lean:117-122`). Third, a
bound on the game in which the *deployed* verifier queries a **lazily sampled random oracle**, and the
adversary's `prove` queries are answered by the honest prover through the same oracle.

Classical recursion (an outer AIR that verifies an inner proof) has to evaluate the inner verifier's
Fiat–Shamir and Merkle hashing **inside the AIR**. An AIR can only arithmetise a *concrete* function
(SHA-256 through L5). Several things follow:

1. The outer AIR's semantic statement is "there is an inner proof that `V^{sha256}` accepts". Turning that
   into "the inner statement is true" needs soundness of the inner protocol *with SHA-256 in place of the
   oracle*, i.e. a standard-model or knowledge assumption about SHA-256. The ROM branch carries no such
   hypothesis. The standard-model branch (`CRSecure`) admits only an explicit reduction **to SHA-256
   collisions**, and no such reduction is known for Fiat–Shamir-compiled multi-round IOPs. This is the
   assessment already recorded in `docs/zk-formal/V3-D0-DESIGN.md` §5.5 ("recursion is rejected: it cannot
   be proved in the ROM game").
2. In the ROM game, the oracle the inner verifier would use and the function the outer AIR computes are
   different objects. "The circuit computes H" cannot even be stated for a lazily sampled H with an
   exponential-size table.
3. `ProverComplete` must hold for **every** `H`, including constant `H`. Any design whose honest prover
   relies on the structure of SHA-256 (arithmetisation-friendliness, a non-degenerate oracle) is
   inadmissible by construction.

The theory literature places recursion in the **arithmetized random oracle model (AROM)**
(Chen–Chiesa–Spooner, "On Succinct Non-Interactive Arguments in Relativized Worlds", EUROCRYPT 2022)
or in the standard model with non-falsifiable assumptions. Neither is in the arena's admission theorem
today.

## 2. Options this track must evaluate

Every option must end in a **closed `AdmissionStatement`** of the existing form, unless the lead
explicitly approves a profile or admission-theorem change (option R4).

| Id | Option | Composition mechanism | ROM-admissible today? | Expected cost shape |
|---|---|---|---|---|
| **R1** | **One STARK, many segment tables, global buses** | All S segments are committed in one proof transcript. The machine state crosses segment boundaries through the *global* grand-product buses (RAM, call stack, gas, host state), so no hash commitment to state is needed. The challenges come after all commitments, and the prover runs in two passes and streams segments. | **Yes.** It is our existing protocol with more tables, and soundness is the existing L2/L3 argument. | Proof size and verify time grow linearly in S (openings per table per query). The prover's peak memory stays at one segment if it re-executes. FRI batching amortises only the low-degree test. |
| **R2** | **Native accumulation (non-recursive folding)** | A Reed–Solomon / IOP accumulation scheme (Arc, WARP or similar), where the *deployed* verifier natively runs all S cheap accumulation-verifier steps, hashing included, and then one decider. No verifier runs in-circuit. | **Plausibly.** The oracle is used only by the native verifier. The accumulation soundness must be proved in our ROM game with a union bound over S. | Proof is S × (accumulation messages) + 1 decider. It must beat R1 by a constant factor large enough to matter. Requires a new L3-style soundness development. |
| **R3** | **Full recursive verification (verifier-in-AIR, IVC/PCD)** | The outer AIR verifies inner proofs over a concrete hash, possibly with folding to make the step cheap. | **No** (§1). | Smallest proofs. Inadmissible without R4. |
| **R4** | **Admission-theorem extension** | Add an AROM-style or "hash-is-oracle-and-arithmetised" branch to `CryptoSound`, or allow a SHA-256 knowledge assumption in a new profile. | Only by changing governance. | This is a policy decision, not engineering. It must come with a written argument for why the weaker guarantee is acceptable for NEAR validation. |
| **R5** | **No composition** | D3 stays capped at `G_α`. The cap is raised only by larger tables, more columns per row, a better RAM layout or prover speed. | Yes | Bounded by a single proof's capacity (DESIGN §8 LDE limits). |

Also in scope, because R1 and R2 need it: the **segmentation semantics itself**. That is a Lean
definition of the NEAR-WASM machine state at a segment boundary, together with
`run = compose (segments)`, proved for the W3 interpreter of `near-wasm-strategy.md` §1. The machine state
covers pc, frames, operand stack, locals, linear memory, globals, table, gas counter and its WASM-side
global, the stack budget, registers, promises, logs, and the storage overlay with the recorded-proof
counter.

## 3. What must be proven (evidence class P unless noted)

For the option(s) chosen at the decision point:

1. **Segmentation correctness**: `NearWasm.run cfg s = foldSegments cfg (split s)` for every split
   respecting the boundary rules. This is a pure semantics lemma, independent of the proof system.
2. **Composition soundness in the ROM game**, as a `RomSound … tapeLen num den` bound for the composed
   verifier with `num · 2^targetBits ≤ den` at the profile's query budgets (2^64 hash, 2^40 prove), with
   S up to `S_max` (≥ 1,000).
   * R1 reduces to the existing L2/L3 extraction and potential argument over a larger table family. The
     new work is the bus balance across segments and the bounded-height side conditions for S tables.
   * R2 needs an accumulation soundness proof in the unique-decoding regime (as L3 does for FRI).
     Errors are union-bounded over S steps. Proximity gaps and correlated agreement must be either
     proved Mathlib-free or avoided.
3. **Completeness for every `H`** (`ProverComplete`), including degenerate `H`. No grinding, no
   rejection sampling on hash outputs (`DESIGN.md` R3/R4).
4. **Semantic soundness and completeness** of the segment AIR tables against the segmentation
   semantics (1). These are the per-table lemmas of D3 §2.3.2, extended by boundary-state
   consistency on the global buses.
5. **Verifier connection**: the composed verifier is a `TreeVerifier`/`OracleVerifier` with a proved
   query bound (`romSound_of_potential` needs a bounded query count; DESIGN §4 proof format).
6. **For R4 only**: a written threat-model document approved by the lead *before* any Lean work, plus
   the new branch defined in `ArenaCore` with a proof that the existing branches are unchanged.

## 4. Acceptance criteria

The track is **done** when one of the following holds, and the lead records the decision in
`D3_WASM_REQUIREMENTS.md` §2.5.

**(A) Composition adopted (R1 or R2).**
1. All of §3 items 1–5 are proved: kernel-checked, no `sorry`/`axiom`/`native_decide`, axioms ⊆
   {propext, Classical.choice, Quot.sound}, Mathlib-free in trusted modules.
2. A **PoC challenge** with a toy segmented machine (for example the checkpoint-1 PoC subset, at least
   2^24 operators over at least 8 segments) is ADMITTED live at formal tier, passing all six checker gates.
3. Measured cost curves (proof bytes, verify time, prove time, peak memory vs S) at S ∈ {1, 8, 64, 512}.
   These include the projection to 10^15 gas, and show whether the D3 caps can be met. If they can't, the
   report says so explicitly.
4. A hostile suite: a forged boundary state, a dropped or duplicated segment, reordered segments, and a
   segment proved with another segment's challenges. Each must be rejected at its intended gate.

**(B) Composition rejected (R5).** A written analysis showing that R1 and R2 cannot meet any
reasonable D3 caps, or that their soundness cannot be closed in the ROM game. It must include the
measured R1 curve from (A).3 as evidence. D3 then remains capped, and `G_α` work moves to the prover lane.

**(C) Escalation (R4).** Only on explicit lead and user approval, after (B) or a partial (A).

## 5. Constraints

* Reuse L1–L4 and their proofs. Fork nothing. New protocol pieces get their own lane (like L2/L3).
* No Mathlib in trusted modules (F4). Kernel `decide` only for side conditions.
* Host resource rules: heavy commands go through `/data/illia/nearproof-deps/bin/heavy` with
  `taskset -c 8-15,24-31`.
* Effort is honest research scale. R1's protocol work is small, and its cost is linear proof size. R2 is a
  research-grade soundness development (comparable to L3, likely 15–30k LOC). Nothing in the literature
  gives R3 inside our admission theorem.

## 6. Checkpoints

1. Segmentation semantics (§3.1) defined for the PoC subset and proved, plus R1 cost model calibrated on
   the existing prover.
2. Decision memo: R1 vs R2 (vs R5), with the measured R1 curve.
3. Composition soundness (§3.2–3.5) proved for the chosen option.
4. PoC challenge ADMITTED, plus the hostile suite (§4.A.2–4).
