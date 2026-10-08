import ZkFormal.NearV3.Render.Ups.CompactExtract.KidsBytes
import ZkFormal.NearV3.Extract.Ups.BranchK
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  (hsc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x)
  {o ℓ ci ti di si ki sdi : Nat} (K : PartK s o ℓ ci ti di si ki sdi)
include hw hs hsc K

/-- **The layout of a branch part.** -/
theorem brLay {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) (htl : s.row o qtl = 0) (hte : s.row o qte = 0) :
    ∃ c0, BrLay s o ℓ w c0 ci ti di si ki sdi := by
  have hq0 : s.row o qb = 1 := by simpa using K.qb 0 K.pos
  have hlt0 : o < s.rows.length := by have := K.le; have := K.pos; omega
  obtain ⟨-, -, b1, b2, hsum, -, -, -⟩ := partHead (okRow hw hs hlt0) (rowLt hw hs _) K.pf hq0
  have hle := K.le
  -- a field's rows, with the state predicate
  have fieldF := fun {r n g : Nat} (hU : UField s r n) (hst : stOf (s.row r) = g) (h1 : o ≤ r) (h2 : r + n ≤ o + ℓ) =>
    kField hw hs hsc K hU hst h1 h2
  rcases b2 with hb2 | hb2
  · -- without a value
    have hb1 : s.row o qtb1 = 1 := by omega
    obtain ⟨hℓ, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, W, ⟨U5, s5⟩⟩ := branchNShape hw hs U hb1 hq0 K.pf
    refine ⟨3, Or.inl ⟨rfl, hb1, hb2⟩, by omega, ?_, ?_, W, ?_, U5, s5⟩
    · rw [hBy, show (3 : Nat) = 1 + 2 from rfl, rowsB_append, List.append_assoc]
    · intro d hd
      rcases (show d = 0 ∨ 1 ≤ d by omega) with rfl | h
      · have F := fieldF U0 s0 (by omega) (by omega) 0 (by omega)
        simp only [Nat.add_zero] at F ⊢
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        have t := (stOf_inv a1).1 a2
        have := a1.sum; have := a1.bs
        exact ⟨a1, a3, a4, a5, a6, by omega, by omega, by omega, ⟨fun _ => trivial, fun _ => t⟩, ⟨fun h => by omega, fun h => by omega⟩,
          fun _ h => by omega, fun _ h => by omega⟩
      · have F := fieldF U1 s1 (by omega) (by omega) (d - 1) (by omega)
        rw [show o + 1 + (d - 1) = o + d by omega] at F
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        have t := (stOf_inv a1).2.2.2.2.2.2.1 a2
        have := a1.sum; have := a1.bs
        have hfs := U1.fs (d - 1) (by omega)
        rw [show o + 1 + (d - 1) = o + d by omega] at hfs
        exact ⟨a1, a3, a4, a5, a6, by omega, by omega, by omega, ⟨fun h => by omega, fun h => by omega⟩, ⟨fun _ => by omega, fun _ => t⟩,
          fun h _ => by have := hfs.1 h; omega, fun _ h => hfs.2 (by omega)⟩
    · intro d hd
      have hWe := W (d / 32) (by omega)
      have F := fieldF hWe.1 hWe.2 (by omega) (by omega) (d % 32) (by omega)
      rw [show o + 3 + 32 * (d / 32) + d % 32 = o + 3 + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, (stOf_inv a1).2.2.2.2.2.2.2.1 a2⟩
  · -- with a value
    obtain ⟨hℓ, hBy, ⟨U0, s0⟩, ⟨U1, s1⟩, ⟨U2, s2⟩, ⟨U3, s3⟩, W, ⟨U5, s5⟩⟩ := branchVShape hw hs U hb2 hq0 K.pf
    refine ⟨39, Or.inr ⟨rfl, by omega, hb2⟩, by omega, ?_, ?_, W, ?_, U5, s5⟩
    · rw [hBy, show (39 : Nat) = 1 + (4 + (32 + 2)) from rfl, rowsB_append, rowsB_append, rowsB_append]
      simp only [List.append_assoc, show o + 1 + 4 = o + 5 by omega, show o + 5 + 32 = o + 37 by omega]
    · intro d hd
      rcases (show d = 0 ∨ (1 ≤ d ∧ d < 5) ∨ (5 ≤ d ∧ d < 37) ∨ 37 ≤ d by omega) with rfl | h | h | h
      · have F := fieldF U0 s0 (by omega) (by omega) 0 (by omega)
        simp only [Nat.add_zero] at F ⊢
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        have t := (stOf_inv a1).1 a2
        have := a1.sum; have := a1.bs
        exact ⟨a1, a3, a4, a5, a6, by omega, by omega, by omega, ⟨fun _ => trivial, fun _ => t⟩, ⟨fun h => by omega, fun h => by omega⟩,
          fun _ h => by omega, fun _ h => by omega⟩
      · have F := fieldF U1 s1 (by omega) (by omega) (d - 1) (by omega)
        rw [show o + 1 + (d - 1) = o + d by omega] at F
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        have t := (stOf_inv a1).2.2.2.2.1 a2
        have := a1.sum; have := a1.bs
        exact ⟨a1, a3, a4, a5, a6, by omega, by omega, by omega, ⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩,
          fun _ h => by omega, fun h _ => by omega⟩
      · have F := fieldF U2 s2 (by omega) (by omega) (d - 5) (by omega)
        rw [show o + 5 + (d - 5) = o + d by omega] at F
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        have t := (stOf_inv a1).2.2.2.2.2.1 a2
        have := a1.sum; have := a1.bs
        exact ⟨a1, a3, a4, a5, a6, by omega, by omega, by omega, ⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩,
          fun _ h => by omega, fun h _ => by omega⟩
      · have F := fieldF U3 s3 (by omega) (by omega) (d - 37) (by omega)
        rw [show o + 37 + (d - 37) = o + d by omega] at F
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
        have t := (stOf_inv a1).2.2.2.2.2.2.1 a2
        have := a1.sum; have := a1.bs
        have hfs := U3.fs (d - 37) (by omega)
        rw [show o + 37 + (d - 37) = o + d by omega] at hfs
        exact ⟨a1, a3, a4, a5, a6, by omega, by omega, by omega, ⟨fun h => by omega, fun h => by omega⟩, ⟨fun _ => by omega, fun _ => t⟩,
          fun h _ => by have := hfs.1 h; omega, fun _ h => hfs.2 (by omega)⟩
    · intro d hd
      have hWe := W (d / 32) (by omega)
      have F := fieldF hWe.1 hWe.2 (by omega) (by omega) (d % 32) (by omega)
      rw [show o + 39 + 32 * (d / 32) + d % 32 = o + 39 + d by omega] at F
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := F
      exact ⟨a1, a3, a4, a5, a6, (stOf_inv a1).2.2.2.2.2.2.2.1 a2⟩

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
