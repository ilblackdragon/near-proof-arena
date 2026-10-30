import NearSpecV3.ChunkValidationD1
import NearSpecV3.D0SubD1.Work.Root.Basic
import NearSpecV3.D0SubD1.Work.Root.Rel
import NearSpecV3.D0SubD1.Work.Root.Phases
import NearSpecV3.D0SubD1.Work.Root.Outcome
import NearSpecV3.D0SubD1.Work.Decode.Agree
import NearSpecV3.D0SubD1.Work.Runtime.EmptyTxs
import NearSpecV3.D0SubD1.Work.Phases.PhaseA
import NearSpecV3.D0SubD1.Work.Phases.PhaseB
import NearSpecV3.D0SubD1.Work.Phases.PhaseC
import NearSpecV3.D0SubD1.Work.Phases.PhaseD
import NearSpecV3.D0SubD1.Work.Phases.PhaseE

/-!
# `D0 ⊆ D1`: every `RelD0`-accepted pair is `RelD1`-accepted

`checkD0` and `checkD1CoreObs` are two ~90-statement `Except String` do-blocks.  They are cut,
each, into five *phases* (`NearSpecV3.D0SubD1.Work.Root.Phases`, cuts `A … E` at statement boundaries), and
the chain identities

* `checkD0 cb wb = d0PA cb wb d0K0`,
* `checkD1CoreObs cb wb = d1PA cb wb d1K0`

are **definitional** (`Phases.d0_chain`, `Phases.d1_chain` are `rfl`).  Each phase lemma
(`Work.Phases.PhaseA … PhaseE`) is a simulation statement in the vocabulary of
`NearSpecV3.D0SubD1.Work.Root.Rel`:

* `SIM x y` — `y` succeeds whenever `x` does,
* `WRel w wD` — the D1 witness of a D0-accepted stream: shared fields equal, both transaction
  lists empty (this is `Work.Decode.Agree`),
* `ORel out outD` — the D1 runtime output on the empty transaction list: same trie, outgoing
  receipts, gas and tokens, no local ids, and the outcomes decorated by `OStatus.value`
  (this is `Work.Runtime.EmptyTxs`).

Two extra invariants ride along the continuation chain because they are *created* before they are
*used*: `c.txValid = []` (D0 checks `c.txValid.isEmpty` in phase B, D1 checks
`c.txValid.length == w.txs.length` in phase D) and `decide (receipts.map receiptId).Nodup = true`
(D0 checks it in phase D, D1 checks `out.localIds ++ receipts.map receiptId` in phase E).
`Work.Root.Outcome` turns the `OStatus.value` decoration of the outcomes into the equality of the
two outcome roots at the header comparison.

The proof below is only this composition: the five phase lemmas applied along the chain, and the
verdict projection `checkD1 = (checkD1CoreObs).map (fun _ => ())`.

Provenance: proved by a deepseek-fv run (DeepSeek V4.1 flash agents, 2026-10-28) against the
statement `RelD0 cb w → RelD1 cb w` with no Mathlib; accepted by the lean-eval comparator
(axioms: `propext`, `Quot.sound`, `Classical.choice`). The `Work/` tree is that run's lemma tree,
only renamed into this namespace.
-/

namespace NearSpecV3.D0SubD1

open NearSpec NearSpecV3

set_option maxHeartbeats 0

theorem relD0_imp_relD1 : ∀ (cb w : NearSpec.Bytes), NearSpecV3.RelD0 cb w → NearSpecV3.RelD1 cb w := by
  intro cb wb h
  -- Unpack the D0 verdict: `checkD0` succeeded.
  have hok : NearSpecV3.checkD0 cb wb = .ok () := by
    unfold NearSpecV3.RelD0 NearSpecV3.acceptsD0 at h
    cases hc : NearSpecV3.checkD0 cb wb with
    | ok u => cases u; rfl
    | error e => rw [hc] at h; exact absurd h (by simp)
  -- **The lockstep**: the five phases, glued by their continuations.  Each `Phase` call is the
  -- next phase applied to the continuation built from the remaining ones; the two invariants
  -- (`c.txValid = []` from `PhaseB`, `(receipts.map receiptId).Nodup` from `PhaseD`) are
  -- threaded through the continuation hypotheses exactly where the second checker needs them.
  have lockstep : NearSpecV3.D0SubD1.Work.Root.SIM (NearSpecV3.checkD0 cb wb)
      (NearSpecV3.checkD1CoreObs cb wb) := by
    rw [NearSpecV3.D0SubD1.Work.Root.d0_chain,
      show NearSpecV3.checkD1CoreObs cb wb =
        NearSpecV3.D0SubD1.Work.Root.d1PA cb wb NearSpecV3.D0SubD1.Work.Root.d1K0 from rfl]
    exact Work.Phases.PhaseA cb wb NearSpecV3.D0SubD1.Work.Root.d0K0 NearSpecV3.D0SubD1.Work.Root.d1K0
      (fun c swBytes =>
        Work.Phases.PhaseB c swBytes NearSpecV3.D0SubD1.Work.Root.d0K1 NearSpecV3.D0SubD1.Work.Root.d1K1
          (fun w wD H L hw hT =>
            Work.Phases.PhaseC c w wD H L hw NearSpecV3.D0SubD1.Work.Root.d0K2 NearSpecV3.D0SubD1.Work.Root.d1K2
              (fun idx B2 prevB2 slotB2 implicitBlks receipts =>
                Work.Phases.PhaseD c hT w wD H L idx B2 prevB2 slotB2 implicitBlks receipts hw
                  NearSpecV3.D0SubD1.Work.Root.d0K3 NearSpecV3.D0SubD1.Work.Root.d1K3
                  (fun out outD own ho hN =>
                    Work.Phases.PhaseE c w wD H L idx B2 slotB2 implicitBlks receipts out outD own
                      hw ho hN))))
  -- The D1 observable checker succeeds, hence so does its projection.
  obtain ⟨o, ho⟩ := lockstep () hok
  have h1 : NearSpecV3.checkD1 cb wb = .ok () :=
    (NearSpecV3.checkD1CoreObs_agrees cb wb).1 ⟨o, ho⟩
  unfold NearSpecV3.RelD1 NearSpecV3.acceptsD1
  rw [h1]

end NearSpecV3.D0SubD1

namespace NearSpecV3

/-- D0 ⊂ D1: every pair the D0 checker accepts, the D1 checker accepts (checker level). For the
rungs of the `near-chunk-v3-1` statement (`RelRungDk := RelD3 ∧ InRungDk`, `RungsDefs.lean`) the
inclusion is a projection, `rungD0_rungD1`; this checker-level theorem is what admits a `checkD0`
accept into the D1 domain (`Rungs.rungD0_of_checks`). -/
theorem relD0_relD1 (cb w : NearSpec.Bytes) (h : RelD0 cb w) : RelD1 cb w :=
  D0SubD1.relD0_imp_relD1 cb w h

end NearSpecV3
