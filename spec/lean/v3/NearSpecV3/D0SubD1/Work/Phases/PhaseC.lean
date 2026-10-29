import NearSpecV3.ChunkValidationD1
import NearSpecV3.D0SubD1.Work.Root.Basic
import NearSpecV3.D0SubD1.Work.Root.Rel
import NearSpecV3.D0SubD1.Work.Root.Phases

/-! Proof notes (the statement and route this lemma was proved against):

Phase C of the D0 ⊆ D1 lockstep. `Work.Root.d0PC c w H L k` / `d1PC c wD H L k2` (`NearSpecV3.D0SubD1.Work.Root.Phases`) are the THIRD SLICE of the two checkers — the chain-segment walk and the source-receipt loop. The two slices are **byte-identical** once `wD` and `w` are related: every statement reads only `w.entries` (`lookupLast key w.entries`) and `w.appliedReceiptsHash` among the witness fields.

`SIM x y` is `∀ a, x = .ok a → ∃ b, y = .ok b`; `hw : WRel w wD` gives `wD.entries = w.entries` as `hw.2.2.2.2.1` and `wD.appliedReceiptsHash = w.appliedReceiptsHash` as `hw.2.2.2.2.2.1`.

PROOF (complete, verified): the six `let x ← match Y with | some … => pure … | none => throw …`
statements in the slice each elaborate, inside the do-block, to a **`have`-headed `match`** whose
arms apply the rest of the slice (`have __do_jp := fun x => REST; match Y with | some b => pure b >>= __do_jp | none => throw e >>= __do_jp`).  Such a term is neither a `bind` of a shared
scrutinee (`sim_bind_same` refuses) nor the shape of `sim_match_pure_throw_bind` (whose `none` arm
is `throw e >>= K` *at one answer type*, while ours has different continuations at different answer
types).  The fix is a bare **`cases` on the scrutinee**, which splits both sides at once, followed by
**`dsimp only`** to beta/zeta-reduce the `have` in the branch — that leaves `SIM (pure i >>= K) (pure i >>= K')`, closed by `sim_bind_same`.  The `none` arm of these statements is closed by
`sim_throw` (the whole D0 run is `.error`).  The two `for` loops have the *same term* on both sides
(their answer type is their own state type, not the do-block's), so `sim_bind_same` peels them
directly.  The two trailing `check`s are shared terms.
-/

namespace Work.Phases

theorem PhaseC (c : NearSpecV3.Claim) (w : NearSpecV3.StateWitness) (wD : NearSpecV3.StateWitnessD1) (H : NearSpecV3.ChunkInner) (L : NearSpecV3.Layout)
    (hw : NearSpecV3.D0SubD1.Work.Root.WRel w wD)
    (k : NearSpecV3.Claim → NearSpecV3.StateWitness → NearSpecV3.ChunkInner → NearSpecV3.Layout → Nat → NearSpecV3.Blk → NearSpecV3.Blk → NearSpecV3.ChunkInner → List NearSpecV3.Blk → List NearSpec.Receipt → Except String Unit)
    (k2 : NearSpecV3.Claim → NearSpecV3.StateWitnessD1 → NearSpecV3.ChunkInner → NearSpecV3.Layout → Nat → NearSpecV3.Blk → NearSpecV3.Blk → NearSpecV3.ChunkInner → List NearSpecV3.Blk → List NearSpec.Receipt → Except String NearSpecV3.Observable)
    (hk : ∀ (idx : Nat) (B2 : NearSpecV3.Blk) (prevB2 : NearSpecV3.Blk) (slotB2 : NearSpecV3.ChunkInner)
      (implicitBlks : List NearSpecV3.Blk) (receipts : List NearSpec.Receipt),
      NearSpecV3.D0SubD1.Work.Root.SIM (k c w H L idx B2 prevB2 slotB2 implicitBlks receipts)
        (k2 c wD H L idx B2 prevB2 slotB2 implicitBlks receipts)) :
    NearSpecV3.D0SubD1.Work.Root.SIM
      (NearSpecV3.D0SubD1.Work.Root.d0PC c w H L k)
      (NearSpecV3.D0SubD1.Work.Root.d1PC c wD H L k2) := by
  unfold NearSpecV3.D0SubD1.Work.Root.d0PC NearSpecV3.D0SubD1.Work.Root.d1PC
  rw [show wD.entries = w.entries from hw.2.2.2.2.1,
      show wD.appliedReceiptsHash = w.appliedReceiptsHash from hw.2.2.2.2.2.1]
  apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro blks
  repeat' (first | (apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro x))
  cases L.index H.shardId with
  | none => exact NearSpecV3.D0SubD1.Work.Root.sim_throw _ _
  | some i =>
    dsimp only
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro idx
    repeat' (first | (apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro x))
    cases List.findIdx? (fun b => match b.slots[idx]? with
        | some (s, _) => s.heightIncluded == b.hdr.height | none => false) blks with
    | none => exact NearSpecV3.D0SubD1.Work.Root.sim_throw _ _
    | some j =>
      dsimp only
      apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro b2i
      cases blks[b2i]? with
      | none => exact NearSpecV3.D0SubD1.Work.Root.sim_throw _ _
      | some b =>
        dsimp only
        apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro B2
        repeat' (first | (apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro x))
        cases List.findIdx? (fun b => match b.slots[idx]? with
            | some (s, _) => s.heightIncluded == b.hdr.height | none => false)
            (List.drop (b2i + 1) blks) with
        | none => exact NearSpecV3.D0SubD1.Work.Root.sim_throw _ _
        | some j2 =>
          dsimp only
          apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro stop
          repeat' (first | (apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro x))
          cases blks[b2i + 1]? with
          | none => exact NearSpecV3.D0SubD1.Work.Root.sim_throw _ _
          | some b =>
            dsimp only
            apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro prevB2
            cases B2.slots[idx]? with
            | none => exact NearSpecV3.D0SubD1.Work.Root.sim_throw _ _
            | some p =>
              dsimp only
              apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro slotB2
              apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro st
              apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro u
              apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same; intro u2
              exact hk _ _ _ _ _ _

end Work.Phases
