# Lane `lane/v3-bus` — `np-udr-stark-v2` (public-message bus): status

Design: `V3-D0-DESIGN.md` §2.4, §6 and §10 (decision 2: v2 is a new protocol version, and v1
stays byte-for-byte unchanged).
v1 is untouched. No existing definition or proof is modified. Everything v2 lives in
`zk-formal/ZkFormal/V2/` and in a new section of `FORMATS.md` (§8).

Rules: no `sorry`, `axiom` or `native_decide`.

## Statements

| deliverable | statement | file | state |
|---|---|---|---|
| L4 | `PubSeg`, `AirP` (extends `Air`), `pubMsgs`, `pubCount`, `pubFit`, `HoldsP` | `V2/Air.lean` | built |
| L4 | `holdsP_iff_holds` (no segments ⇒ `HoldsP ↔ Holds`), `holdsP_ofAir` | `V2/Air.lean` | built |
| L4 | `AirP.wf` (with `pubBound`, `multBoundP`, `fpBoundP`), `AirP.wf_air` (⇒ v1 `Air.wf`) | `V2/Air.lean` | built |
| L4 | `globalChecksP`, `prepP`, `Iop.verifierP`, `verifierP`, `prepP_eq`, `checksPass_eq`, `globalChecksP_nil` | `V2/Verifier.lean` | built |
| L4 | export `np-air-v2` (`AirP.exportJson`) + `FORMATS.md` §8 | `V2/Export.lean` | written |
| L3 | `rbrWithP_of` (composition, `PubBad` disjunct) | `V2/Np/Compose.lean` | built |
| L3 | `msg0P msg2P msg6P chal5P chal7P` | `V2/Np/Early.lean` | written, build pending |
| L3 | `chal1P chal3P` (gpAlpha/gpGamma on trace ++ public multisets) | `V2/Np/Bus.lean` | written, build pending |
| L3 | `msg4P` (`finals_gp`, `no_gpDifferP`) | `V2/Np/Msg4.lean` | written, build pending |
| L3 | `msg8P` (`globalChecksP_true`, `pubProd_eq`) | `V2/Np/Msg8.lean` | written, build pending |
| L3 | `msgLateP chalLateP` | `V2/Np/Late.lean` | written, build pending |
| L3 | `queryP` (`deepSemQ`, `localBridgeQ`, `goodQ`, `qdataP`) | `V2/Np/Query.lean` | written, build pending |
| L3 | **`rbrWithP`**, `rbrFactsP` | `V2/Np/Main.lean` | written, build pending |
| L2 | **`stark_romSound_fullP`** (`schedOkP`, `npBoundsP`, `verifierP_queryBound`) | `V2/RomFull.lean` | written, build pending |
| L7 | **`npIopCompleteP`** (`busProdP`, `globalP`, `localNH`, `proverWfP`) | `V2/Prover.lean` | written, build pending |
| L7 | **`admission_v2`**, `np_proverCompleteP` | `V2/Admission.lean` | written, build pending |
| P1 | `sizeMaxSched`, `sizeBound_le_sched`, `sizeMaxSched_le` | `V2/SizeSched.lean` | helper, in progress |
| toy | toy AIR with a public segment and a hint, admission theorem | `V2/Toy.lean` | not started |
| P2 | `NpOkP` with `auxGroup ∈ {1,2,3}` | — | open, see below |

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

(to be filled from `lake build` runs)
