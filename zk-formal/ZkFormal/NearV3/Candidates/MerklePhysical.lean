import ZkFormal.NearV3.Candidates.MerkleBranches

namespace ZkFormal.NearV3.Candidates.MerkleEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

/-- Proof-only projection of one physical table to the old extractor's index.
No witness cells, constraints or verifier inputs are added. -/
def focus (tr : Trace Fp) (tt : Nat) : Trace Fp :=
  {log:=fun _ => tr.log tt,cell:=fun _ => tr.cell tt}

theorem focus_eval (tr : Trace Fp) (tt t r : Nat) (pub : List Fp) (e : Expr) :
    e.eval (focus tr tt) t r pub=e.eval tr tt r pub := rfl

theorem focus_local {tr : Trace Fp} {tt : Nat} {pub : List Fp} {T : Air.Table}
    (h : TableLocal T tr tt pub) (t : Nat) : TableLocal T (focus tr tt) t pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    exact h.constr r hr e he
  · intro r hr i hi e he
    exact h.bits r hr i hi e he

theorem focus_mult (tr : Trace Fp) (tt t r : Nat) (pub : List Fp) (es : List Expr) (k : Nat) :
    Interaction.multNat.go (focus tr tt) t r pub es k=Interaction.multNat.go tr tt r pub es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp only [Interaction.multNat.go,focus_eval,ih]; rfl

theorem focus_count (tr : Trace Fp) (tt t : Nat) (pub : List Fp)
    (is : List Interaction) (b : Nat) (sd : Bool) (m : List Fp) :
    tableBusCount is (focus tr tt) t pub b sd m=tableBusCount is tr tt pub b sd m := by
  have hi : ∀ i : Interaction, ∀ r,
      i.multNat (focus tr tt) t r pub=i.multNat tr tt r pub := by
    intro i r
    exact focus_mult tr tt t r pub i.mult 0
  have hm : ∀ i : Interaction, ∀ r,
      i.msgVal (focus tr tt) t r pub=i.msgVal tr tt r pub := by
    intro i r
    apply List.map_congr_left
    intro e he
    rfl
  simp only [tableBusCount,hi,hm]
  rfl

/-- Semantic view and exact physical traffic at ANY position in the assembled
candidate family, not only the old table numbering. -/
theorem physical_nonempty_view {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal table tr tt pub) (hc : countE.eval tr tt 0 pub≠0) :
    ∃ v, MrkWf (MerklePublic.aliasPublic pub) v ∧
      TableTraffic table.interactions tr tt pub (mrkTraffic (MerklePublic.aliasPublic pub) v) := by
  obtain ⟨v,hw,ht⟩ := nonempty_view (focus_local h T_MRK) hc
  refine ⟨v,hw,?_⟩
  intro b m
  simpa only [focus_count] using ht b m

end ZkFormal.NearV3.Candidates.MerkleEmpty
