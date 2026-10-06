# Lane `lane/v3-bus` — `np-udr-stark-v2` (public-message bus): status

Design: `V3-D0-DESIGN.md` §2.4, §6 and §10 (decision 2: v2 is a new protocol version, and v1
stays byte-for-byte unchanged).
v1 is untouched. No existing definition or proof is modified. Everything v2 lives in
`zk-formal/ZkFormal/V2/` and in a new section of `FORMATS.md` (§8).

Rules: no `sorry`, `axiom` or `native_decide`.

## Statements

All of these are built, contain no `sorry`, `axiom` or `native_decide`, and use axioms
⊆ {propext, Classical.choice, Quot.sound}. Each was checked with `#print axioms`.

| deliverable | statement | file | axioms |
|---|---|---|---|
| L4 | `PubSeg`, `AirP` (extends `Air`), `pubMsgs`, `pubCount`, `pubFit`, `HoldsP` | `V2/Air.lean` | — |
| L4 | `holdsP_iff_holds` (no segments ⇒ `HoldsP ↔ Holds`), `holdsP_ofAir` | `V2/Air.lean` | propext |
| L4 | `AirP.wf` (`pubBound`, `multBoundP`, `fpBoundP`), `AirP.wf_air` (⇒ v1 `Air.wf`) | `V2/Air.lean` | propext |
| L4 | `globalChecksP`, `prepP`, `globalOkP`, `Iop.verifierP`, `verifierP`; `prepP_eq`, `checksPass_eq`, `globalChecksP_nil` | `V2/Verifier.lean` | propext |
| L4 | export `np-air-v2` (`AirP.exportJson`), `FORMATS.md` §8 | `V2/Export.lean` | — |
| L3 | `rbrWithP_of`; rounds `msg0P msg2P msg4P msg6P msg8P msgLateP chal1P chal3P chal5P chal7P chalLateP queryP` | `V2/Np/*.lean` | std3 |
| L3 | **`V2.Np.rbrWithP`** : `NpOkP AP prm → RbrWith (Iop.verifierP Fp Fp8 AP prm) (AirLangP AP) Fp8.all 2^36 (agreeUdr prm.logBlowup) (DoomedP AP prm)`; `rbrFactsP` | `V2/Np/Main.lean` | std3 |
| L2 | **`V2.stark_romSound_fullP`**: ROM soundness at 2^-128 for `verifierP`, language `AirLangP` (`schedOkP`, `npBoundsP`, `verifierP_queryBound`) | `V2/RomFull.lean` | std3 |
| L7 | **`Prover.Np.npIopCompleteP`**: v1's honest prover is perfectly complete for the v2 IOP on `HoldsP` traces (`busProdP`, `globalP`, `localNH`, `proverWfP`, `reach_v1`) | `V2/Prover.lean` | std3 |
| L7 | **`V2.admission_v2`**: guard ∘ `V3.hintTree` ∘ v2 STARK, composed with `V3.romSound_hint` and `romSound_guard`; `np_proverCompleteP` | `V2/Admission.lean` | std3 |
| P1 | `SizeSched.sizeMaxSched`, **`sizeBound_le_sched`** (any `prm`), **`sizeMaxSched_le`** (≤ `sizeMax … κ`), `near_sizeMaxSched = 5,473,967` (was 7,426,175), `near_size_sched`, `toy_size_sched` | `V2/SizeSched.lean`, `V2/SizeSchedNear.lean` | std3 / propext |
| toy | **`V2.Toy.toyP_admission`**: closed `AdmissionStatement` for a sorted-permutation toy. The claim and the hint (the sorted witness) are two public segments on one bus. Native `prep` checks sortedness. Soundness is `toy_soundP`, completeness `toy_compP`. | `V2/Toy.lean` | std3 |
| P2 | `NpOkP` with `auxGroup ∈ {1,2,3}` | — | **open**, see below |

(std3 = propext, Classical.choice, Quot.sound.)

### Findings

* **P1 saving is ≈1.95 MB, not ≈3 MB.** The design estimate (§5.3) leaves out commits forced
  by roll-ins. `nearAir` has 7 tables, so up to 6 layers can be forced to commit by a
  roll-in, which adds 1,050,624 B in the worst case. Without roll-ins the bound would be
  4,423,343 B, which matches the design's ≈4.4 MB. `sizeMaxSched nearAir = 5,473,967 B`.
  The design's v3 numbers in §5.3 (≈5.2–5.6 MB at the formal bound) should be raised by about 1 MB.
  Alternatively, prove a tighter constraint on roll-in positions.
* The toy's inner STARK bound is `sizeMaxSched toyAir = 2,829,897 B`.

## Design notes and findings

* **The count encoding.** The verifier's public vector is the claim's bytes, so a
  segment's record count is a little-endian u32 over 4 public bytes (`PubSeg.count`).
  The design sketch (§2.4) left this open.
* **Static bound.** Without a static bound on how many public messages can exist, the
  fingerprint and grand-product bad-challenge counts (`fpBound`, `multBound`) are
  unbounded. A count of up to `2^32` with width 0 would also give up to `2^32`
  messages. Fix: `AirP.maxPub` and the `fits` condition `start + n·w ≤ min(|cb|, maxPub)`,
  checked by the verifier and required by `HoldsP`, plus `width ≥ 1` in `AirP.wf`.
  `holdsP_iff_holds` still holds exactly, because `fits` is vacuous without segments.
* **`AirP.wf` is a static side condition** (`NpOkP`), not part of the verifier's header
  check. This keeps v2's header check, schedule and shape *definitionally* v1's, so all
  of v1's shape, schedule and frame lemmas apply unchanged (`shaped_iff`, `slots_eq`).
* **Reuse.** v1's statement-level L3 theorems are stated for v1's `Stage` and v1's
  `global`, so they cannot be instantiated for v2 (v2's doomed stages differ in the bus
  disjunct). All of v1's *lemma-level* results are reused. The round proofs are copies
  with the bus disjunct replaced: about 1.5 k lines, generated from the v1 text where
  possible. The query-phase lemmas of v1 use `global` only through the structural record
  `QData`. They are restated with `QData` as the hypothesis, which is generic in the AIR.
* **Completeness.** The honest prover is v1's: the proof bytes are identical, and the
  verifier recomputes the public products. v1's local lemmas use `Holds` only through
  `constr`/`bits`. They are re-stated for `HoldsP` (copies). `localStmt` never used `Holds`.

## Open

* **P2 (`auxGroup ∈ {1,2,3}`).** Not done. v1's `Msg4` (`table_fins`, `tabOk_of` via
  `numGroups_one`), `Ali.csAt_length` and `Chal7.table_deg` are specialised to
  `auxGroup = 1`, and so is the prover model (`dp = Params.default`). Soundness for
  `g ∈ {2,3}` needs generalised copies of these, about 0.5–1 k lines. Completeness needs a
  prover model parameterised by `prm`, which means copying `Prover/Np*` (about 4.5 k lines).
  `NpOkP` currently requires `prm = Params.default`.

## Elaboration times

From `lake build` on this host, CPUs 8–15, against a warm v1 cache. Every v2 module elaborates in
under about 20 s. The largest are `V2/Prover.lean` (≈5–10 s), `V2/Np/Query.lean` (≈8 s),
`V2/Np/Late.lean` (≈8 s) and `V2/SizeSchedNear.lean` (5.8 s, kernel evaluation on
`nearAir`). Each of the rest takes under 2 s. All of v2 adds about 1 minute to an
elaboration budget. A per-file timing run was interrupted by host memory pressure
(the shared `zkbuild.slice` was pinned at its 40 GB `MemoryHigh` by another lane's job),
so these numbers are approximate.

## Process notes

* `zk-formal/ZkFormal.lean` (root import) is not modified. The v2 modules are built by name
  (`lake build ZkFormal.V2.Toy ZkFormal.V2.SizeSchedNear ZkFormal.V2.Export`). Adding them to the
  root is left to the lead.
