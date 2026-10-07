import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractRoots

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt cap : Nat}

/-- The window/segment equations are unchanged on every candidate row. -/
theorem row_shape (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) :
    (tr.cell tt r wf=1 → tr.cell tt r sg=1 ∧ tr.cell tt r pw=0) ∧
    (tr.cell tt r wl=1 → tr.cell tt r sg=1 ∧ tr.cell tt r pw=31) ∧
    tr.cell tt r sf=tr.cell tt r wf*(1-tr.cell tt r wn) ∧
    tr.cell tt r sl=tr.cell tt r wl*(tr.cell tt r wn+tr.cell tt r lf) := by
  have h1 := con hL hr (.mul (c wf) (Dsl.not (c sg))) (by decide +kernel)
  have h2 := con hL hr (.mul (c wf) (c pw)) (by decide +kernel)
  have h3 := con hL hr (.mul (c wl) (Dsl.not (c sg))) (by decide +kernel)
  have h4 := con hL hr (.mul (c wl) (sub (c pw) (k 31))) (by decide +kernel)
  have h5 := con hL hr (sub (c sf) (.mul (c wf) (Dsl.not (c wn)))) (by decide +kernel)
  have h6 := con hL hr (sub (c sl) (.mul (c wl) (.add (c wn) (c lf)))) (by decide +kernel)
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_k] at h1 h2 h3 h4 h5 h6
  exact ⟨fun h => ⟨by grind, by grind⟩, fun h => ⟨by grind, by grind⟩, by grind, by grind⟩

theorem segment_first_active (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hs : tr.cell tt r sf=1) : tr.cell tt r sg=1 := by
  have hh := row_shape hL hr
  rcases isBool hL hr (x := wf) (by simp [SrcpProof.bools]) with hw | hw
  · rw [hh.2.2.1, hw] at hs; exfalso; grind
  · exact (hh.1 hw).1

theorem segment_last_active (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hs : tr.cell tt r sl=1) : tr.cell tt r sg=1 := by
  have hh := row_shape hL hr
  rcases isBool hL hr (x := wl) (by simp [SrcpProof.bools]) with hw | hw
  · rw [hh.2.2.2, hw] at hs; exfalso; grind
  · exact (hh.2.1 hw).1

/-- Global first-row metadata remains exact even with duplicate skipping. -/
theorem row0 (hL : TableLocal (DedupTable.table cap) tr tt pub) :
    tr.cell tt 0 rt=1 ∧ tr.cell tt 0 j=0 ∧ tr.cell tt 0 q=0 ∧ tr.cell tt 0 sz=tr.cell tt 0 L := by
  have hp : 0<tr.height tt := Nat.two_pow_pos _
  have h1 := con hL hp (.mul .isFirst (Dsl.not (c rt))) (by decide +kernel)
  have h2 := con hL hp (.mul .isFirst (c j)) (by decide +kernel)
  have h3 := con hL hp (.mul .isFirst (c q)) (by decide +kernel)
  have h4 := con hL hp (.mul .isFirst (sub (c sz) (c L))) (by decide +kernel)
  simp only [eval_mul, eval_not, eval_c, eval_sub, eval_isFirst, ite_true] at h1 h2 h3 h4
  exact ⟨by grind, by grind, by grind, by grind⟩

/-- A physical last segment is complete; a duplicate root may instead be the
logical final active row. -/
theorem last_segment (hL : TableLocal (DedupTable.table cap) tr tt pub)
    (hs : tr.cell tt (tr.height tt-1) sg=1) : tr.cell tt (tr.height tt-1) sl=1 := by
  have hp : 0<tr.height tt := Nat.two_pow_pos _
  have hh := con hL (r := tr.height tt-1) (by omega)
    (.mul .isLast (.mul (c sg) (Dsl.not (c sl)))) (by decide +kernel)
  have he : tr.height tt-1+1=tr.height tt := by omega
  simp only [eval_mul, eval_c, eval_not, eval_isLast, he, ite_true, hs] at hh
  grind

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
