import ZkFormal.NearV3.Rcpt.Candidates.DedupRootUnit

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra SrcpV3
open SrcpProof (uFirst isOne)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem row0_sg (h0 : 0 < tr.height tt) : tr.cell tt 0 sg = 0 := by
  have he := disjoint hL h0
  rw [(row0 hL).1] at he
  grind

/-- A successor segment cannot wrap around to row zero. -/
theorem next_sg_not_wrap {r : Nat} (hr : r < tr.height tt)
    (hs : tr.cell tt ((r + 1) % tr.height tt) sg = 1) : r + 1 < tr.height tt := by
  apply Classical.byContradiction
  intro hn
  have he : r + 1 = tr.height tt := by omega
  rw [he, Nat.mod_self, row0_sg hL (by omega)] at hs
  exact absurd hs (by decide)

/-- Every segment followed by another segment is followed by a full 64-row path unit. -/
theorem next_path_unit {r : Nat} (hr : r < tr.height tt) (hl : tr.cell tt r sl = 1)
    (hs : tr.cell tt ((r + 1) % tr.height tt) sg = 1) :
    r + 1 + 64 ≤ tr.height tt ∧ IsU tr tt (r + 1) 64 ∧
    tr.cell tt (r + 1) rt = 0 ∧ tr.cell tt (r + 1) lf = 0 ∧
    (tr.cell tt (r + 1) q).toNat = (tr.cell tt r q).toNat + 1 ∧
    tr.cell tt (r + 1) pl = 64 - 32 * tr.cell tt r lf ∧
    ∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hn := next_sg_not_wrap hL hr hs
  rw [SrcpProof.nxt hn] at hs
  have hf := afterSegSg hL hn hl hs
  have huFirst : uFirst tr tt (r + 1) = true := by simp [uFirst, isOne, hf.1]
  obtain ⟨ℓ, hH, hu⟩ := seg_from (segFacts hL) (r + 1) hn huFirst
  have hnrt : tr.cell tt (r + 1) rt = 0 := by
    have he := disjoint hL hn
    rw [hs] at he; grind
  have h64 : ℓ = 64 := by
    rcases (segShape hL hu hH hnrt).1 with h | h
    · rw [hf.2.1] at h; exact False.elim (by simpa using h.1)
    · exact h.2
  subst ℓ
  exact ⟨hH, hu, hnrt, hf.2.1, path_q_succ hL hn hl hs, hf.2.2.2.1, hf.2.2.2.2⟩

/-- The predecessor digest length is 32 after a leaf and 64 after a path. -/
theorem next_path_length {r : Nat} (hr : r < tr.height tt) (hl : tr.cell tt r sl = 1)
    (hs : tr.cell tt ((r + 1) % tr.height tt) sg = 1) :
    (tr.cell tt (r + 1) pl).toNat = if tr.cell tt r lf = 1 then 32 else 64 := by
  have he := (next_path_unit hL hr hl hs).2.2.2.2.2.1
  rcases isBool hL hr (x := lf) (by simp [SrcpProof.bools]) with hf | hf
  · rw [he, hf]
    decide +kernel
  · rw [he, hf]
    decide +kernel

/-- Extract the Boolean path direction without leaving a decoding obligation. -/
theorem path_direction {s : Nat} (hs : s < tr.height tt) :
    tr.cell tt s dir = (if decide (tr.cell tt s dir = 1) then 1 else 0) := by
  rcases isBool hL hs (x := dir) (by simp [SrcpProof.bools]) with hd | hd <;> simp [hd]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
