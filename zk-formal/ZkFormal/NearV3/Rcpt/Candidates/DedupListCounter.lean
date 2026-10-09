import ZkFormal.NearV3.Rcpt.Candidates.DedupRootCarry

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem active_prev {r : Nat} (hr : r + 1 < tr.height tt)
    (ha : tr.cell tt (r + 1) rt = 1 ∨ tr.cell tt (r + 1) sg = 1) :
    tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1 := by
  rcases isBool hL (by omega : r < _) (x := rt) (by simp [SrcpProof.bools]) with ht | ht
  · rcases isBool hL (by omega : r < _) (x := sg) (by simp [SrcpProof.bools]) with hs | hs
    · have hp := padStep hL hr ht hs
      rcases ha with ha | ha <;> simp_all
    · exact Or.inr hs
  · exact Or.inl ht

/-- The list counter starts at zero and increases only at subsequent root rows. -/
theorem list_counter_nat {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    ∃ n, n ≤ r ∧ tr.cell tt r j = Fp.ofNat n := by
  induction r with
  | zero => exact ⟨0, by omega, (row0 hL).2.1⟩
  | succ r ih =>
    have hr' : r < tr.height tt := by omega
    have ha' := active_prev hL hr ha
    obtain ⟨n, hn, hj⟩ := ih hr' ha'
    rcases isBool hL hr' (x := rt) (by simp [SrcpProof.bools]) with ht | ht
    · have hs : tr.cell tt r sg = 1 := by rcases ha' with h | h; simp_all; exact h
      rcases isBool hL hr' (x := sl) (by simp [SrcpProof.bools]) with hl | hl
      · exact ⟨n, by omega, ((inSeg hL hr hs hl).2.2.1 j (by simp [listConst])).trans hj⟩
      · rcases isBool hL hr (x := sg) (by simp [SrcpProof.bools]) with hnsg | hnsg
        · have hnrt : tr.cell tt (r + 1) rt = 1 := by rcases ha with h | h; exact h; simp_all
          refine ⟨n + 1, by omega, ?_⟩
          rw [(afterSegRt hL hr hl hnrt).2, hj,
            show (1 : Fp) = Fp.ofNat 1 from rfl, ofNat_add']
        · exact ⟨n, by omega, ((afterSegSg hL hr hl hnsg).2.2.2.2 j (by simp [listConst])).trans hj⟩
    · rcases isBool hL hr' (x := dup) (by simp [SrcpProof.bools]) with hd | hd
      · exact ⟨n, by omega, (computed_list_carry hL hr ht hd j (by simp [listConst])).trans hj⟩
      · refine ⟨n+1, by omega, ?_⟩
        rw [(duplicate_active_step hL hr hd ha).2.2, hj,
          show (1 : Fp) = Fp.ofNat 1 from rfl, ofNat_add']

theorem list_counter_bound {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    (tr.cell tt r j).toNat ≤ r := by
  obtain ⟨n, hn, he⟩ := list_counter_nat hL hr ha
  have hnP : n < P := by have := hP hL; omega
  rw [he, Fp.toNat_ofNat, Nat.mod_eq_of_lt hnP]
  exact hn

/-- RC identifiers are canonical as well as SRC identifiers. -/
theorem list_id_lt {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    msgId K_RC (tr.cell tt r j).toNat < P := by
  have hc := list_counter_bound hL hr ha
  have hH := height_le hL
  unfold msgId K_RC P
  omega

/-- Completed computations advance the natural source index exactly once. -/
theorem list_j_succ {r : Nat} (hr : r+1<tr.height tt)
    (hl : tr.cell tt r sl=1) (ht : tr.cell tt (r+1) rt=1) :
    (tr.cell tt (r+1) j).toNat=(tr.cell tt r j).toNat+1 := by
  apply toNat_succ_of (afterSegRt hL hr hl ht).2
  have hc := list_counter_bound hL (by omega) (active_prev hL hr (Or.inl ht))
  have hh := hP hL
  omega

/-- Skipped occurrences also advance the natural source index exactly once. -/
theorem duplicate_j_succ {r : Nat} (hr : r+1<tr.height tt)
    (hd : tr.cell tt r dup=1) (ht : tr.cell tt (r+1) rt=1) :
    (tr.cell tt (r+1) j).toNat=(tr.cell tt r j).toNat+1 := by
  apply toNat_succ_of (duplicate_active_step hL hr hd (Or.inl ht)).2.2
  have hc := list_counter_bound hL (by omega) (active_prev hL hr (Or.inl ht))
  have hh := hP hL
  omega

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
