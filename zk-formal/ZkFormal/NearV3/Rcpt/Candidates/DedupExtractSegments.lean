import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractShape

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt cap : Nat}
variable (hL : TableLocal (DedupTable.table cap) tr tt pub)
include hL

/-- Ordinary segment semantics recovered row-by-row, without the old table cap. -/
theorem inSeg {r : Nat} (hr : r + 1 < tr.height tt) (hs : tr.cell tt r sg = 1) (hl : tr.cell tt r sl = 0) :
    tr.cell tt (r + 1) sg = 1 ∧ tr.cell tt (r + 1) rt = 0 ∧
    (∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x) ∧
    (∀ x ∈ segConst, tr.cell tt (r + 1) x = tr.cell tt r x) := by
  have hr' : r < tr.height tt := by omega
  have hold := old_segment_row hL hr' hs
  have k1 := fun x (hx : x ∈ listConst) => hold (e := mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem
      (f := fun x => mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) hx)))))
  have k2 := fun x (hx : x ∈ segConst) => hold (e := mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inr (List.mem_map_of_mem (f := fun x => mul3 (c sg) (Dsl.not (c sl)) (sub (n x) (c x))) hx)))
  -- the next row is active and a segment row
  have hw := isBool hL hr' (x := wl) (by simp [SrcpProof.bools])
  have hn : tr.cell tt (r + 1) sg = 1 := by
    rcases hw with hw | hw
    · have h1 := hold (e := mul3 (c sg) (Dsl.not (c wl)) (Dsl.not (n sg))) (by simp [SrcpV3.constraints])
      simp only [eval_mul3, eval_c, eval_n, eval_not, SrcpProof.nxt hr, hs, hw] at h1; grind
    · have h1 := hold (e := mul3 (c wl) (Dsl.not (c sl)) (Dsl.not (n sg))) (by simp [SrcpV3.constraints])
      simp only [eval_mul3, eval_c, eval_n, eval_not, SrcpProof.nxt hr, hl, hw] at h1; grind
  have hrt : tr.cell tt (r + 1) rt = 0 := by
    have := disjoint hL (r := r + 1) hr; rw [hn] at this; grind
  refine ⟨hn, hrt, fun x hx => ?_, fun x hx => ?_⟩
  · have := k1 x hx; simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, SrcpProof.nxt hr, hs, hl] at this; grind
  · have := k2 x hx; simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, SrcpProof.nxt hr, hs, hl] at this; grind

/-- Inside a window. -/
theorem inWin {r : Nat} (hr : r + 1 < tr.height tt) (hs : tr.cell tt r sg = 1) (hw : tr.cell tt r wl = 0) :
    tr.cell tt (r + 1) wf = 0 ∧ tr.cell tt (r + 1) pw = tr.cell tt r pw + 1 ∧
    tr.cell tt (r + 1) wn = tr.cell tt r wn ∧
    ∀ x, x < 31 → tr.cell tt (r + 1) (reg x) = tr.cell tt r (reg (x + 1)) := by
  have hr' : r < tr.height tt := by omega
  have hold := old_segment_row hL hr' hs
  have h1 := hold (e := mul3 (c sg) (Dsl.not (c wl)) (n wf)) (by simp [SrcpV3.constraints])
  have h2 := hold (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n pw) (.add (c pw) (k 1))))
    (by simp [SrcpV3.constraints])
  have h3 := hold (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n wn) (c wn))) (by simp [SrcpV3.constraints])
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, SrcpProof.nxt hr, hs, hw] at h1 h2 h3
  refine ⟨by grind, by grind, by grind, fun x hx => ?_⟩
  have h4 := hold (e := mul3 (c sg) (Dsl.not (c wl)) (sub (n (reg x)) (c (reg (x + 1))))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inr (List.mem_map_of_mem (f := fun x => mul3 (c sg) (Dsl.not (c wl))
      (sub (n (reg x)) (c (reg (x + 1))))) (List.mem_range.2 hx)))
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, SrcpProof.nxt hr, hs, hw] at h4
  grind

/-- From the first window of a path segment to the second. -/
theorem winSwitch {r : Nat} (hr : r + 1 < tr.height tt) (hw : tr.cell tt r wl = 1) (hl : tr.cell tt r sl = 0) :
    tr.cell tt (r + 1) wf = 1 ∧ tr.cell tt (r + 1) wn = 1 := by
  have hr' : r < tr.height tt := by omega
  have hs : tr.cell tt r sg = 1 := ((row_shape hL hr').2.1 hw).1
  have hold := old_segment_row hL hr' hs
  have h1 := hold (e := mul3 (c wl) (Dsl.not (c sl)) (Dsl.not (n wf))) (by simp [SrcpV3.constraints])
  have h2 := hold (e := mul3 (c wl) (Dsl.not (c sl)) (Dsl.not (n wn))) (by simp [SrcpV3.constraints])
  simp only [eval_mul3, eval_c, eval_n, eval_not, SrcpProof.nxt hr, hw, hl] at h1 h2
  exact ⟨by grind, by grind⟩

/-- After a segment: a path segment of the same list. -/
theorem afterSegSg {r : Nat} (hr : r + 1 < tr.height tt) (hl : tr.cell tt r sl = 1)
    (hs : tr.cell tt (r + 1) sg = 1) :
    tr.cell tt (r + 1) sf = 1 ∧ tr.cell tt (r + 1) lf = 0 ∧ tr.cell tt (r + 1) q = tr.cell tt r q + 1 ∧
    tr.cell tt (r + 1) pl = 64 - 32 * tr.cell tt r lf ∧
    ∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hr' : r < tr.height tt := by omega
  have hold := old_segment_row hL hr' (segment_last_active hL hr' hl)
  have h1 := hold (e := mul3 (c sl) (n sg) (Dsl.not (n sf))) (by simp [SrcpV3.constraints])
  have h2 := hold (e := mul3 (c sl) (n sg) (n lf)) (by simp [SrcpV3.constraints])
  have h3 := hold (e := mul3 (c sl) (n sg) (sub (n q) (.add (c q) (k 1)))) (by simp [SrcpV3.constraints])
  have h4 := hold (e := mul3 (c sl) (n sg) (sub (n pl) (sub (k 64) (smul 32 (c lf)))))
    (by simp [SrcpV3.constraints])
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, eval_smul, SrcpProof.nxt hr, hl, hs]
    at h1 h2 h3 h4
  refine ⟨by grind, by grind, by grind, by grind, fun x hx => ?_⟩
  have h5 := hold (e := mul3 (c sl) (n sg) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun x => mul3 (c sl) (n sg) (sub (n x) (c x))) hx))))
  simp only [eval_mul3, eval_c, eval_n, eval_sub, SrcpProof.nxt hr, hl, hs] at h5
  grind


end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
