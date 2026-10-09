import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractSegments

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl SrcpV3
open SrcpProof (isOne uAct uFirst uLast)

variable {tr : Trace Fp} {pub : List Fp} {tt cap : Nat}
variable (hL : TableLocal (DedupTable.table cap) tr tt pub)
include hL

theorem zero_of_not_one {r x : Nat} (hr : r<tr.height tt)
    (hx : x ∈ SrcpProof.bools ++ [DedupTable.repeated]) (h : isOne tr tt x r=false) :
    tr.cell tt r x=0 := by
  rcases isBool hL hr hx with hz | ho
  · exact hz
  · simp [isOne, ho] at h

/-- Inactive rows remain inactive at every noncyclic transition. -/
theorem padStep {r : Nat} (hr : r+1<tr.height tt)
    (ha : tr.cell tt r rt=0) (hs : tr.cell tt r sg=0) :
    tr.cell tt (r+1) rt=0 ∧ tr.cell tt (r+1) sg=0 := by
  have hh := con hL (r := r) (by omega)
    (mul3 .isTransition (Dsl.not actE) (.add (n rt) (n sg))) (by decide +kernel)
  have hn : r+1≠tr.height tt := by omega
  simp only [eval_mul3, actE, eval_c, eval_n, eval_not, eval_add, eval_isTransition,
    hn, ite_false, SrcpProof.nxt hr, ha, hs] at hh
  have hd := disjoint hL (r := r+1) hr
  rcases mul_eq_zero'.mp hd with hz | hz <;> grind

/-- A root unit is followed either by its leaf or by the next root if skipped. -/
theorem root_next_unit {r : Nat} (hr : r+1<tr.height tt) (ha : tr.cell tt r rt=1)
    (hn : tr.cell tt (r+1) rt=1 ∨ tr.cell tt (r+1) sg=1) :
    tr.cell tt (r+1) rt=1 ∨ tr.cell tt (r+1) sf=1 := by
  have hr' : r<tr.height tt := by omega
  rcases isBool hL hr' (x := dup) (by simp [SrcpProof.bools]) with hd | hd
  · exact Or.inr (computed_after_root hL hr ha hd).2.2.1
  · rcases isBool hL hr' (x := gz) (by simp [SrcpProof.bools]) with hz | hz
    · exact Or.inl (duplicate_step hL hr hd hz).1
    · have hh := con hL hr'
        (.mul .isTransition (.mul (c gz) (.add (n rt) (n sg)))) (by decide +kernel)
      have he : r+1≠tr.height tt := by omega
      simp only [eval_mul, eval_c, eval_n, eval_add, eval_isTransition,
        he, ite_false, SrcpProof.nxt hr, hz] at hh
      have hdis := disjoint hL (r := r+1) hr
      exfalso
      rcases hn with hn | hn <;> grind

/-- Complete root/segment unit decomposition for arbitrary candidate traces.
Skipped roots remain one-row units; no old source height cap is assumed. -/
theorem segFacts : SegFacts (tr.height tt) (uAct tr tt) (uFirst tr tt) (uLast tr tt) where
  first_act r hr h := by
    simp only [uFirst, uAct, isOne, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (segment_first_active hL hr h)
  last_act r hr h := by
    simp only [uLast, uAct, isOne, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (segment_last_active hL hr h)
  cont r hr ha hl := by
    simp only [uLast, uAct, uFirst, isOne, Bool.or_eq_true, decide_eq_true_eq,
      Bool.or_eq_false_iff, decide_eq_false_iff_not] at ha hl ⊢
    have hr' : r<tr.height tt := by omega
    have hs : tr.cell tt r sg=1 := by
      rcases ha with h | h
      · exact absurd h hl.1
      · exact h
    have hl0 : tr.cell tt r sl=0 := zero_of_not_one hL hr'
      (by simp [SrcpProof.bools]) (by simp [isOne, hl.2])
    obtain ⟨hn, hrt, _⟩ := inSeg hL hr hs hl0
    refine ⟨Or.inr hn, by rw [hrt]; decide, ?_⟩
    have hsf := (row_shape hL (r := r+1) hr).2.2.1
    rcases isBool hL hr' (x := wl) (by simp [SrcpProof.bools]) with hw | hw
    · rw [hsf, (inWin hL hr hs hw).1]; grind
    · rw [hsf, (winSwitch hL hr hw hl0).2]; grind
  next r hr hl ha := by
    simp only [uLast, uAct, uFirst, isOne, Bool.or_eq_true, decide_eq_true_eq] at hl ha ⊢
    rcases hl with hl | hl
    · exact root_next_unit hL hr hl ha
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (afterSegSg hL hr hl ha).1
  pad r hr ha := by
    simp only [uAct, isOne, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ha ⊢
    have h1 := zero_of_not_one hL (r := r) (by omega) (x := rt)
      (by simp [SrcpProof.bools]) (by simp [isOne, ha.1])
    have h2 := zero_of_not_one hL (r := r) (by omega) (x := sg)
      (by simp [SrcpProof.bools]) (by simp [isOne, ha.2])
    obtain ⟨e1, e2⟩ := padStep hL hr h1 h2
    rw [e1, e2]
    exact ⟨by decide, by decide⟩
  start _ := by simp [uFirst, isOne, (row0 hL).1]
  stop _ ha := by
    simp only [uAct, uLast, isOne, Bool.or_eq_true, decide_eq_true_eq] at ha ⊢
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (last_segment hL ha)

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
