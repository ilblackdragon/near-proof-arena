import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractBoundary

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem height_le : tr.height tt ≤ 2^24 := by
  have hh := hL.log_le
  change tr.log tt ≤ 24 at hh
  exact Nat.pow_le_pow_right (by decide) hh

/-- Active rows have a bounded natural message counter, positive inside segments. -/
theorem counter_nat {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    ∃ n, n ≤ r ∧ tr.cell tt r q = Fp.ofNat n ∧ (tr.cell tt r sg = 1 → 0 < n) := by
  induction r with
  | zero =>
    have h0 := row0 hL
    refine ⟨0, by omega, h0.2.2.1, ?_⟩
    intro hs
    have he := disjoint hL hr
    rw [h0.1, hs] at he
    exact False.elim (by grind)
  | succ r ih =>
    have hr' : r < tr.height tt := by omega
    have ha' : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1 := by
      rcases isBool hL hr' (x := rt) (by simp [SrcpProof.bools]) with ht | ht
      · rcases isBool hL hr' (x := sg) (by simp [SrcpProof.bools]) with hs | hs
        · have hp := padStep hL hr ht hs
          rcases ha with ha | ha <;> simp_all
        · exact Or.inr hs
      · exact Or.inl ht
    obtain ⟨n, hn, hq, hp⟩ := ih hr' ha'
    have incr (he : tr.cell tt (r + 1) q = tr.cell tt r q + 1) :
        tr.cell tt (r + 1) q = Fp.ofNat (n + 1) := by
      rw [he, hq, show (1 : Fp) = Fp.ofNat 1 from rfl, ofNat_add']
    rcases isBool hL hr' (x := rt) (by simp [SrcpProof.bools]) with ht | ht
    · have hs : tr.cell tt r sg = 1 := by rcases ha' with h | h; simp_all; exact h
      rcases isBool hL hr' (x := sl) (by simp [SrcpProof.bools]) with hl | hl
      · have he := (inSeg hL hr hs hl).2.2.2 q (by simp [segConst])
        exact ⟨n, by omega, he.trans hq, fun _ => hp hs⟩
      · rcases isBool hL hr (x := sg) (by simp [SrcpProof.bools]) with hnsg | hnsg
        · have hnrt : tr.cell tt (r + 1) rt = 1 := by rcases ha with h | h; exact h; simp_all
          exact ⟨n, by omega, (afterSegRt hL hr hl hnrt).1.trans hq,
            fun h => False.elim (by rw [hnsg] at h; simpa using h)⟩
        · exact ⟨n + 1, by omega, incr (afterSegSg hL hr hl hnsg).2.2.1, by omega⟩
    · rcases isBool hL hr' (x := dup) (by simp [SrcpProof.bools]) with hd | hd
      · exact ⟨n+1, by omega, incr (computed_after_root hL hr ht hd).2.2.2, by omega⟩
      · have hstep := duplicate_active_step hL hr hd ha
        refine ⟨n, by omega, hstep.2.1.trans hq, ?_⟩
        intro hsg
        have hdis := disjoint hL hr
        rw [hstep.1, hsg] at hdis
        exfalso; grind

/-- Canonical extraction recovers the natural counter, with no field wraparound. -/
theorem counter_bound {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    (tr.cell tt r q).toNat ≤ r ∧ (tr.cell tt r sg = 1 → 0 < (tr.cell tt r q).toNat) := by
  obtain ⟨n, hn, he, hp⟩ := counter_nat hL hr ha
  have hnP : n < P := by have := hP hL; omega
  rw [he, Fp.toNat_ofNat, Nat.mod_eq_of_lt hnP]
  exact ⟨hn, hp⟩

/-- Every source-message identifier is canonical in the field. -/
theorem counter_id_lt {r : Nat} (hr : r < tr.height tt)
    (ha : tr.cell tt r rt = 1 ∨ tr.cell tt r sg = 1) :
    msgId K_SRC (tr.cell tt r q).toNat < P := by
  have hc := (counter_bound hL hr ha).1
  have hH := height_le hL
  unfold msgId K_SRC P
  omega


end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
