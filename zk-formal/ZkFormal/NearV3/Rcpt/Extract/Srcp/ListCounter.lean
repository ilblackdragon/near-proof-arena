import ZkFormal.NearV3.Rcpt.Extract.Srcp.SizeTraffic

/-! Canonical list indices and natural counter transitions for block assembly. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

theorem active_prev {r : Nat} (hr : r + 1 < tr.height tt)
    (ha : tr.cell tt (r + 1) rt = 1 ∨ tr.cell tt (r + 1) sg = 1) :
    tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1 := by
  rcases isBool hL (by omega : r < _) (x := rt) (by simp [bools]) with ht | ht
  · rcases isBool hL (by omega : r < _) (x := sg) (by simp [bools]) with hs | hs
    · have hp := padStep hL hr ht hs
      rcases ha with ha | ha <;> simp_all
    · exact Or.inr hs
  · exact Or.inl ht

/-- The list counter starts at zero and increases only at subsequent root rows. -/
theorem list_counter_nat {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    ∃ n, n ≤ r ∧ tr.cell tt r j = Fp.ofNat n := by
  induction r with
  | zero => exact ⟨0, by omega, (row0 hL hr).2.1⟩
  | succ r ih =>
    have hr' : r < tr.height tt := by omega
    have ha' := active_prev hL hr ha
    obtain ⟨n, hn, hj⟩ := ih hr' ha'
    rcases isBool hL hr' (x := rt) (by simp [bools]) with ht | ht
    · have hs : tr.cell tt r sg = 1 := by rcases ha' with h | h; simp_all; exact h
      rcases isBool hL hr' (x := sl) (by simp [bools]) with hl | hl
      · exact ⟨n, by omega, ((inSeg hL hr hs hl).2.2.1 j (by simp [listConst])).trans hj⟩
      · rcases isBool hL hr (x := sg) (by simp [bools]) with hnsg | hnsg
        · have hnrt : tr.cell tt (r + 1) rt = 1 := by rcases ha with h | h; exact h; simp_all
          refine ⟨n + 1, by omega, ?_⟩
          rw [(afterSegRt hL hr hl hnrt).2, hj,
            show (1 : Fp) = Fp.ofNat 1 from rfl, ofNat_add']
        · exact ⟨n, by omega, ((afterSegSg hL hr hl hnsg).2.2.2.2 j (by simp [listConst])).trans hj⟩
    · exact ⟨n, by omega, ((afterRoot hL hr ht).2.2.2.2 j (by simp [listConst])).trans hj⟩

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

/-- The root-to-leaf increment is an actual natural increment, not field wraparound. -/
theorem root_q_succ {r : Nat} (hr : r + 1 < tr.height tt) (ht : tr.cell tt r rt = 1) :
    (tr.cell tt (r + 1) q).toNat = (tr.cell tt r q).toNat + 1 := by
  apply toNat_succ_of (afterRoot hL hr ht).2.2.2.1
  have hc := (counter_bound hL (by omega) (Or.inl ht)).1
  have hh := hP hL
  omega

/-- The path-to-path increment is an actual natural increment. -/
theorem path_q_succ {r : Nat} (hr : r + 1 < tr.height tt)
    (hl : tr.cell tt r sl = 1) (hs : tr.cell tt (r + 1) sg = 1) :
    (tr.cell tt (r + 1) q).toNat = (tr.cell tt r q).toNat + 1 := by
  apply toNat_succ_of (afterSegSg hL hr hl hs).2.2.1
  have hc := (counter_bound hL (by omega) (active_prev hL hr (Or.inr hs))).1
  have hh := hP hL
  omega

/-- Consecutive source blocks have consecutive natural list indices. -/
theorem list_j_succ {r : Nat} (hr : r + 1 < tr.height tt)
    (hl : tr.cell tt r sl = 1) (ht : tr.cell tt (r + 1) rt = 1) :
    (tr.cell tt (r + 1) j).toNat = (tr.cell tt r j).toNat + 1 := by
  apply toNat_succ_of (afterSegRt hL hr hl ht).2
  have hc := list_counter_bound hL (by omega) (active_prev hL hr (Or.inl ht))
  have hh := hP hL
  omega

end ZkFormal.NearV3.SrcpProof
