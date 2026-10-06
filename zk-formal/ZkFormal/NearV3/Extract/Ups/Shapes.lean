import ZkFormal.NearV3.Extract.Ups.PartK
import ZkFormal.NearV3.Extract.Ups.KindHeads

/-!
# ZkFormal.NearV3.Extract.Ups.Shapes — the field layout of leaf and extension parts (layer 2)

A part whose node is a leaf (`qtl = 1`) is `TAG HPL HPF [KEY] VLEN VH MEM`, an extension
(`qte = 1`) `TAG HPL HPF [KEY] CH MEM`; the hex-prefix bytes `HPF [KEY]` are `qhk` rows
(`nokey` iff `qhk = 1`).  `leafShape` / `extShape` give the row offsets, the byte list as the
concatenation of the fields' bytes and the fields.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

attribute [local irreducible] UpsSeg.row UpsSeg.next

/-- The hex-prefix rows `HPF [KEY]` of a leaf/extension part: `qhk` rows from `r`, the first
`HPF`, the others `KEY`. -/
structure KeyRows (s : UpsSeg) (r q : Nat) : Prop where
  pos : 1 ≤ q
  hpf : UField s r 1 ∧ stOf (s.row r) = 2
  key : 1 < q → UField s (r + 1) (q - 1) ∧ stOf (s.row (r + 1)) = 3
  bytes : rowsB s r q = rowsB s r 1 ++ rowsB s (r + 1) (q - 1)

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

theorem keyRows_of {r : Nat} (h1 : UField s r 1) (h2 : stOf (s.row r) = 2) : KeyRows s r 1 :=
  ⟨Nat.le_refl _, ⟨h1, h2⟩, fun h => absurd h (by omega), by simp [rowsB]⟩

/-- **A leaf part's fields.** -/
theorem leafShape {o ℓ : Nat} {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) (htl : s.row o qtl = 1)
    (hq0 : s.row o qb = 1) (hpf : s.row o pf = 1) :
    let q := s.row o qhk
    ℓ = 49 + q ∧ (s.row o nokey = 1 ↔ q = 1) ∧
    rowsB s o ℓ = rowsB s o 1 ++ (rowsB s (o + 1) 4 ++ (rowsB s (o + 5) q ++ (rowsB s (o + 5 + q) 4 ++
      (rowsB s (o + 9 + q) 32 ++ rowsB s (o + 41 + q) 8)))) ∧
    (UField s o 1 ∧ stOf (s.row o) = 0) ∧ (UField s (o + 1) 4 ∧ stOf (s.row (o + 1)) = 1) ∧ KeyRows s (o + 5) q ∧
    (UField s (o + 5 + q) 4 ∧ stOf (s.row (o + 5 + q)) = 4) ∧
    (UField s (o + 9 + q) 32 ∧ stOf (s.row (o + 9 + q)) = 5) ∧
    (UField s (o + 41 + q) 8 ∧ stOf (s.row (o + 41 + q)) = 8) := by
  intro q
  obtain ⟨-, -, -, -, hsum, bnk, -, hnq⟩ := partHead (okRow hw hs (i := o) (by have := U.le; have := U.pos; omega))
    (rowLt hw hs _) hpf hq0
  obtain ⟨hFA, hBy⟩ := partFieldsAt U
  rw [htl] at hFA hBy
  have hlen := congrArg List.length hBy
  rcases bnk with hnk | hnk
  · simp only [shapeU, hnk, ite_true, List.nil_append, List.cons_append, List.singleton_append,
      show ¬ ((0 : Nat) = 1) by omega, ite_false] at hFA hBy hlen
    simp only [FieldsAt, fieldsB, List.append_nil] at hFA hBy hlen
    obtain ⟨U0, s0, U1, s1, U2, s2, U3, s3, U4, s4, U5, s5, U6, s6, -⟩ := hFA
    have hq1 : 1 < q := by have := U3.pos; omega
    simp only [rowsB, List.length_append, List.length_map, List.length_range] at hlen
    refine ⟨by omega, ⟨fun h => by omega, fun h => by omega⟩, ?_, ⟨U0, s0⟩, ⟨U1, s1⟩, ⟨by omega, ⟨U2, s2⟩,
      fun _ => ⟨U3, s3⟩, ?_⟩, ?_, ?_, ?_⟩
    · rw [hBy, show o + 1 + 4 = o + 5 by omega, show o + 5 + 1 + (q - 1) = o + 5 + q by omega,
        show o + 5 + q + 4 = o + 9 + q by omega, show o + 9 + q + 32 = o + 41 + q by omega,
        show o + 5 + 1 = o + 5 + 1 from rfl]
      rw [show q = 1 + (q - 1) by omega, rowsB_append]
      simp only [List.append_assoc]
      rw [show 1 + (q - 1) = q by omega]
    · have := rowsB_append s (o + 5) 1 (q - 1); rwa [show 1 + (q - 1) = q by omega] at this
    · rw [show o + 5 + q = o + 1 + 4 + 1 + (q - 1) by omega]; exact ⟨U4, s4⟩
    · rw [show o + 9 + q = o + 1 + 4 + 1 + (q - 1) + 4 by omega]; exact ⟨U5, s5⟩
    · rw [show o + 41 + q = o + 1 + 4 + 1 + (q - 1) + 4 + 32 by omega]; exact ⟨U6, s6⟩
  · have hq1 : q = 1 := hnq hnk
    simp only [shapeU, hnk, ite_true, List.nil_append, List.cons_append, List.singleton_append] at hFA hBy hlen
    simp only [FieldsAt, fieldsB, List.append_nil] at hFA hBy hlen
    obtain ⟨U0, s0, U1, s1, U2, s2, U4, s4, U5, s5, U6, s6, -⟩ := hFA
    simp only [rowsB, List.length_append, List.length_map, List.length_range] at hlen
    refine ⟨by omega, ⟨fun _ => hq1, fun _ => hnk⟩, ?_, ⟨U0, s0⟩, ⟨U1, s1⟩, ?_, ?_, ?_, ?_⟩
    · rw [hBy, hq1]
    · rw [hq1, show o + 5 = o + 1 + 4 by omega]; exact keyRows_of hw hs U2 s2
    · rw [hq1, show o + 5 + 1 = o + 1 + 4 + 1 by omega]; exact ⟨U4, s4⟩
    · rw [hq1, show o + 9 + 1 = o + 1 + 4 + 1 + 4 by omega]; exact ⟨U5, s5⟩
    · rw [hq1, show o + 41 + 1 = o + 1 + 4 + 1 + 4 + 32 by omega]; exact ⟨U6, s6⟩

/-- **An extension part's fields.** -/
theorem extShape {o ℓ : Nat} {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) (hte : s.row o qte = 1)
    (hq0 : s.row o qb = 1) (hpf : s.row o pf = 1) :
    let q := s.row o qhk
    ℓ = 45 + q ∧ (s.row o nokey = 1 ↔ q = 1) ∧
    rowsB s o ℓ = rowsB s o 1 ++ (rowsB s (o + 1) 4 ++ (rowsB s (o + 5) q ++ (rowsB s (o + 5 + q) 32 ++ rowsB s (o + 37 + q) 8))) ∧
    (UField s o 1 ∧ stOf (s.row o) = 0) ∧ (UField s (o + 1) 4 ∧ stOf (s.row (o + 1)) = 1) ∧ KeyRows s (o + 5) q ∧
    (UField s (o + 5 + q) 32 ∧ stOf (s.row (o + 5 + q)) = 7) ∧
    (UField s (o + 37 + q) 8 ∧ stOf (s.row (o + 37 + q)) = 8) := by
  intro q
  obtain ⟨-, -, -, -, hsum, bnk, -, hnq⟩ := partHead (okRow hw hs (i := o) (by have := U.le; have := U.pos; omega))
    (rowLt hw hs _) hpf hq0
  obtain ⟨hFA, hBy⟩ := partFieldsAt U
  rw [hte] at hFA hBy
  have htl : s.row o qtl = 0 := by omega
  rw [htl] at hFA hBy
  have hlen := congrArg List.length hBy
  rcases bnk with hnk | hnk
  · simp only [shapeU, hnk, ite_true, show ¬ ((0 : Nat) = 1) by omega, ite_false, List.nil_append, List.cons_append, List.singleton_append,
      show ¬ ((0 : Nat) = 1) by omega, ite_false] at hFA hBy hlen
    simp only [FieldsAt, fieldsB, List.append_nil] at hFA hBy hlen
    obtain ⟨U0, s0, U1, s1, U2, s2, U3, s3, U4, s4, U5, s5, -⟩ := hFA
    have hq1 : 1 < q := by have := U3.pos; omega
    simp only [rowsB, List.length_append, List.length_map, List.length_range] at hlen
    refine ⟨by omega, ⟨fun h => by omega, fun h => by omega⟩, ?_, ⟨U0, s0⟩, ⟨U1, s1⟩, ⟨by omega, ⟨U2, s2⟩,
      fun _ => ⟨U3, s3⟩, ?_⟩, ?_, ?_⟩
    · rw [hBy, show o + 1 + 4 = o + 5 by omega, show o + 5 + 1 + (q - 1) = o + 5 + q by omega,
        show o + 5 + q + 32 = o + 37 + q by omega,
        show o + 5 + 1 = o + 5 + 1 from rfl]
      rw [show q = 1 + (q - 1) by omega, rowsB_append]
      simp only [List.append_assoc]
      rw [show 1 + (q - 1) = q by omega]
    · have := rowsB_append s (o + 5) 1 (q - 1); rwa [show 1 + (q - 1) = q by omega] at this
    · rw [show o + 5 + q = o + 1 + 4 + 1 + (q - 1) by omega]; exact ⟨U4, s4⟩
    · rw [show o + 37 + q = o + 1 + 4 + 1 + (q - 1) + 32 by omega]; exact ⟨U5, s5⟩
  · have hq1 : q = 1 := hnq hnk
    simp only [shapeU, hnk, ite_true, show ¬ ((0 : Nat) = 1) by omega, ite_false, List.nil_append, List.cons_append, List.singleton_append] at hFA hBy hlen
    simp only [FieldsAt, fieldsB, List.append_nil] at hFA hBy hlen
    obtain ⟨U0, s0, U1, s1, U2, s2, U4, s4, U5, s5, -⟩ := hFA
    simp only [rowsB, List.length_append, List.length_map, List.length_range] at hlen
    refine ⟨by omega, ⟨fun _ => hq1, fun _ => hnk⟩, ?_, ⟨U0, s0⟩, ⟨U1, s1⟩, ?_, ?_, ?_⟩
    · rw [hBy, hq1]
    · rw [hq1, show o + 5 = o + 1 + 4 by omega]; exact keyRows_of hw hs U2 s2
    · rw [hq1, show o + 5 + 1 = o + 1 + 4 + 1 by omega]; exact ⟨U4, s4⟩
    · rw [hq1, show o + 37 + 1 = o + 1 + 4 + 1 + 32 by omega]; exact ⟨U5, s5⟩

end

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  (hsc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x)
  {o ℓ ci ti di si ki sdi : Nat} (K : PartK s o ℓ ci ti di si ki sdi)
include hw hs hsc K

/-- **The `MEM` field's bytes**: `u64 (E + (A + B − C))` with the inputs of `memIn`, given the
input limbs `< 2^12` and the emitted bytes `< 256`. -/
theorem memBytesK {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) {r0 : Nat} (hU : UField s r0 8)
    (hst : stOf (s.row r0) = 8) (hend : r0 + 8 = o + ℓ)
    (hb : s.row o eL ≤ 1 ∧ s.row o eS ≤ 1 ∧ s.row o useA ≤ 1 ∧ s.row o bN ≤ 1 ∧ s.row o bL ≤ 1 ∧
      s.row o cO ≤ 1 ∧ s.row o cS ≤ 1)
    (hin : ∀ i, i < 8 → inA (s.row (r0 + i)) < 4096 ∧ inB (s.row (r0 + i)) < 4096 ∧
        inC (s.row (r0 + i)) < 4096 ∧ inE (s.row (r0 + i)) < 4096 ∧ s.row (r0 + i) b < 256) :
    let Lv := s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2
    let Sv := s.row r0 (SR 0) + 256 * s.row r0 (SR 1) + 65536 * s.row r0 (SR 2) + 16777216 * s.row r0 (SR 3)
    rowsB s r0 8 = (NearSpec.u64 (s.row o Kc + s.row o eL * Lv + s.row o eS * Sv +
      (s.row o useA * limbs (fun i => s.row (r0 + i) rb) 8 +
        (s.row o bN * limbs (fun i => s.row (r0 + i) mBv) 8 + s.row o bL * Lv) -
       (s.row o cO * limbs (fun i => s.row (r0 + i) mCv) 8 + s.row o cS * Sv + s.row o Cc)))).map UInt8.toNat := by
  intro Lv Sv
  have M := memOf hw hs U
  simp only at M
  have hr : o + (fl[fl.length - 1]'(by have := U.nonempty; omega)).1 = r0 := by omega
  rw [hr] at M
  obtain ⟨-, -, hM⟩ := M
  obtain ⟨hrx, -, hbx⟩ := hM hin
  obtain ⟨e1, e2, e3, e4⟩ := memIn hw hs hsc K hU hst (by omega) (by omega) hb
  rw [e1, e2, e3, e4] at hrx
  rw [hrx] at hbx
  rw [u64_limbs (fun i hi => (hin i hi).2.2.2.2) hbx]
  rfl

end

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

end

end ZkFormal.NearV3.UpsRows
