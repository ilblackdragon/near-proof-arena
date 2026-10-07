import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractUnitShape

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra SrcpV3
open SrcpProof (isOne uAct uFirst uLast)

/-- Every accepting logical candidate trace is a nonempty consecutive list of
one-row roots and32/64-row leaf/path segments, followed only by padding. -/
theorem extract_units {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal (DedupTable.table 24) tr tt pub) :
    ∃ us : List (Nat × Nat), us≠[] ∧ Consec 0 us ∧ segEnd 0 us≤tr.height tt ∧
      (∀ p ∈ us, IsU tr tt p.1 p.2 ∧
        ((tr.cell tt p.1 rt=1 ∧ p.2=1) ∨
         (tr.cell tt p.1 rt=0 ∧
          ((tr.cell tt p.1 lf=1 ∧ p.2=32) ∨ (tr.cell tt p.1 lf=0 ∧ p.2=64))))) ∧
      (∀ r, segEnd 0 us≤r → r<tr.height tt → uAct tr tt r=false) := by
  have hp : 0<tr.height tt := Nat.two_pow_pos _
  obtain ⟨us, hc, he, hu, hpad⟩ := segments_of (segFacts hL) hp
  have hn : us≠[] := by
    intro hz
    subst us
    have hh := hpad 0 (by simp [segEnd]) hp
    simp [uAct, isOne, (row0 hL).1] at hh
  refine ⟨us, hn, hc, he, ?_, hpad⟩
  intro p hmem
  have hU := hu p hmem
  have hbound : p.1+p.2≤tr.height tt := Nat.le_trans (seg_le_end us 0 hc p hmem).2 he
  refine ⟨hU, ?_⟩
  by_cases hr : tr.cell tt p.1 rt=1
  · exact Or.inl ⟨hr, rootUnit hL hU hr⟩
  · have hz : tr.cell tt p.1 rt=0 := rt_bool hL (by have := hU.1; omega) hr
    exact Or.inr ⟨hz, (segShape hL hU hbound hz).1⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
