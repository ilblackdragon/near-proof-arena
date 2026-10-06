import ZkFormal.NearV3.Extract.Ups.FieldBytes
import ZkFormal.NearV3.Extract.Ups.Windows
import ZkFormal.NearV3.Extract.Ups.Mem
import ZkFormal.NearV3.Extract.Ups.NlfRows
import ZkFormal.NearV3.Extract.Ups.QNodes

/-!
# ZkFormal.NearV3.Extract.Ups.PartBytes — field-by-field byte lists of a node part (layer 2)

The generic part of the per-kind statement `rowsB (part) = nodeEnc (target)`:

* `FieldsAt s r SL` / `fieldsB s r SL`: fields of the (state, length) list `SL` laid out from
  row `r`, and their bytes; `partFieldsAt`: a part's bytes are `fieldsB` of its shape
  `shapeU …` and its fields are laid out as the shape says.
* number encodings: `toNats_u32`, `u64_limbs` (eight byte limbs with value `X mod 2^64` are
  `u64 X`).
* field lemmas: a `TAG` field is the tag byte (`tagField`), an `HPL` field is `u32 qhk`
  (`hplField`), fresh `VLEN`/`VH` fields (`vlenField`, `vhField`, the latter with the
  `DIGEST` register of its first row).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Fields with states and lengths `SL`, laid out from row `r`. -/
def FieldsAt (s : UpsSeg) : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | r, (g, n) :: rest => UField s r n ∧ stOf (s.row r) = g ∧ FieldsAt s (r + n) rest

/-- The bytes of fields laid out from row `r`. -/
def fieldsB (s : UpsSeg) : Nat → List (Nat × Nat) → List Nat
  | _, [] => []
  | r, (_, n) :: rest => rowsB s r n ++ fieldsB s (r + n) rest

theorem fieldsAt_of (s : UpsSeg) (o : Nat) : ∀ (fl : List (Nat × Nat)) (s0 : Nat), Consec s0 fl →
    (∀ q (h : q < fl.length), UField s (o + fl[q].1) fl[q].2) →
    FieldsAt s (o + s0) (fl.map fun p => (stOf (s.row (o + p.1)), p.2)) ∧
    rowsB s (o + s0) (segEnd s0 fl - s0) = fieldsB s (o + s0) (fl.map fun p => (stOf (s.row (o + p.1)), p.2))
  | [], s0, _, _ => by simp [FieldsAt, fieldsB, segEnd, rowsB]
  | (s', ℓ) :: rest, s0, ⟨h1, h2⟩, hF => by
    subst h1
    have ih := fieldsAt_of s o rest (s' + ℓ) h2 (fun q h => hF (q + 1) (by simp; omega))
    have hle := segEnd_ge rest (s' + ℓ) h2
    have h0 := hF 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    simp only [List.map_cons, FieldsAt, fieldsB, segEnd]
    rw [show o + (s' + ℓ) = o + s' + ℓ by omega] at ih
    refine ⟨⟨h0, by first | rfl | trivial, ih.1⟩, ?_⟩
    rw [show segEnd (s' + ℓ) rest - s' = ℓ + (segEnd (s' + ℓ) rest - (s' + ℓ)) by omega, rowsB_append, ih.2]

/-- **A part's fields, as its shape.** -/
theorem partFieldsAt {s : UpsSeg} {o ℓ : Nat} {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) :
    let SL := shapeU (s.row o qtl) (s.row o qte) (s.row o qtb1) (s.row o nokey) (s.row o qhk) w
    FieldsAt s o SL ∧ rowsB s o ℓ = fieldsB s o SL := by
  intro SL
  have := fieldsAt_of s o fl 0 U.consec (fun q h => (U.fields q h).1)
  rw [U.cover, U.shape, Nat.add_zero, Nat.sub_zero] at this
  exact this

theorem fieldsAt_len {s : UpsSeg} : ∀ (SL : List (Nat × Nat)) (r : Nat), FieldsAt s r SL → ∀ p ∈ SL, 0 < p.2
  | [], _, _, p, hp => by simp at hp
  | (g, n) :: rest, r, ⟨hU, _, hR⟩, p, hp => by
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hU.pos
    · exact fieldsAt_len rest (r + n) hR p hp

/-! ## Number encodings -/

theorem toNat_u8 (x : Nat) : (UInt8.ofNat x).toNat = x % 256 := by
  simp

theorem toNats_leN : ∀ (n x : Nat), (NearSpec.leN n x).map UInt8.toNat = (List.range n).map fun i => x / 256 ^ i % 256
  | 0, _ => rfl
  | n + 1, x => by
    simp only [NearSpec.leN, List.map_cons, toNat_u8, toNats_leN n (x / 256), List.range_succ_eq_map,
      List.map_map, Function.comp_def, Nat.pow_zero, Nat.div_one, Nat.pow_succ', Nat.div_div_eq_div_mul, Nat.mod_mod]

theorem toNats_u32 (x : Nat) : (NearSpec.u32 x).map UInt8.toNat = [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256] := by
  simp [NearSpec.u32, toNats_leN, List.range_succ]

theorem toNats_u64 (x : Nat) : (NearSpec.u64 x).map UInt8.toNat =
    [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256, x / 4294967296 % 256,
     x / 1099511627776 % 256, x / 281474976710656 % 256, x / 72057594037927936 % 256] := by
  simp [NearSpec.u64, toNats_leN, List.range_succ]

theorem limbs8 (f : Nat → Nat) : limbs f 8 = f 0 + 256 * f 1 + 65536 * f 2 + 16777216 * f 3 + 4294967296 * f 4 +
    1099511627776 * f 5 + 281474976710656 * f 6 + 72057594037927936 * f 7 := by
  simp only [limbs]; omega

/-- Eight byte limbs of value `X mod 2^64` are `u64 X`. -/
theorem u64_limbs {f : Nat → Nat} (hf : ∀ i, i < 8 → f i < 256) {X : Nat} (h : limbs f 8 = X % 2 ^ 64) :
    (NearSpec.u64 X).map UInt8.toNat = (List.range 8).map f := by
  rw [toNats_u64, limbs8] at *
  have := hf 0 (by omega); have := hf 1 (by omega); have := hf 2 (by omega); have := hf 3 (by omega)
  have := hf 4 (by omega); have := hf 5 (by omega); have := hf 6 (by omega); have := hf 7 (by omega)
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem rowsB_one (s : UpsSeg) (r : Nat) : rowsB s r 1 = [s.row r b] := by simp [rowsB]

theorem rowsB_four (s : UpsSeg) (r : Nat) :
    rowsB s r 4 = [s.row r b, s.row (r + 1) b, s.row (r + 2) b, s.row (r + 3) b] := by
  simp [rowsB, List.range_succ]

theorem rowsB_eq_map (s : UpsSeg) (r n : Nat) {f : Nat → Nat} (h : ∀ d, d < n → s.row (r + d) b = f d) :
    rowsB s r n = (List.range n).map f := by
  apply List.map_congr_left; intro d hd; exact h d (List.mem_range.mp hd)

/-! ## Row lemmas: digest lookups -/

theorem dI_nat {dI τ : Nat} (hd : dI < P)
    (h : ((dI : Nat) : Fp) = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * ((τ : Nat) : Fp) + 0)) :
    dI = upsIdN τ 0 := by
  rw [← cast0, ← natCast_mul, ← natCast_add, ← natCast_mul, ← natCast_add] at h
  have := congrArg Fp.toNat h
  simp only [natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt hd] at this
  unfold upsIdN; exact this

theorem dIj_nat {dI τ jj : Nat} (hd : dI < P)
    (h : ((dI : Nat) : Fp) = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * ((τ : Nat) : Fp) + ((jj : Nat) : Fp))) :
    dI = upsIdN τ jj := by
  rw [← natCast_mul, ← natCast_add, ← natCast_mul, ← natCast_add] at h
  have := congrArg Fp.toNat h
  simp only [natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt hd] at this
  unfold upsIdN; exact this

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- The first row of a fresh window looks up `DIGEST`. -/
theorem gDrow (hq : C qb = 1) (hfs : C fs = 1) (hw3 : C wt3 = 0)
    (hW : (C sVH = 1 ∧ C cp = 0 ∧ C sCH = 0) ∨ (C sCH = 1 ∧ C wfr = 1 ∧ C sVH = 0)) : C gD = 1 := by
  have f := factN ok hC hD (e := sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3))) (memDigest (by simp [cDigest]))
  simp only [winFr] at f
  nev_simp at f
  have := hC gD
  rw [P_lit] at this
  rcases hW with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [hq, hfs, hw3, h1, h2, h3] at f <;> omega

end

/-! ## Field rows -/

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- The rows of a field (inside a part): one-hot, the field's state. -/
theorem fieldRowSt {r n g : Nat} (hU : UField s r n) (hst : stOf (s.row r) = g) (hlt : r + n ≤ s.rows.length)
    (hq : ∀ d, d < n → s.row (r + d) qb = 1) :
    ∀ d, d < n → OneHot (s.row (r + d)) ∧ stOf (s.row (r + d)) = g := by
  intro d hd
  have hoh := oneHot hw hs (r := r + d) (by omega) (hq d hd)
  refine ⟨hoh, ?_⟩
  rw [← hst]; unfold stOf
  rw [hU.st d hd sHPL (by simp [states]), hU.st d hd sHPF (by simp [states]), hU.st d hd sKEY (by simp [states]),
    hU.st d hd sVLEN (by simp [states]), hU.st d hd sVH (by simp [states]), hU.st d hd sBM (by simp [states]),
    hU.st d hd sCH (by simp [states]), hU.st d hd sMEM (by simp [states])]

/-- **A `TAG` field**: the tag byte of the part's type. -/
theorem tagField {r : Nat} (hU : UField s r 1) (hst : stOf (s.row r) = 0) (hlt : r + 1 ≤ s.rows.length)
    (hq : s.row r qb = 1) (hpf : s.row r pf = 1) :
    rowsB s r 1 = [s.row r qtb1 + 2 * s.row r qtb2 + 3 * s.row r qte] := by
  have R := fieldRowSt hw hs hU hst hlt (fun d hd => by rw [show d = 0 by omega, Nat.add_zero]; exact hq) 0 (by omega)
  simp only [Nat.add_zero] at R
  have h1 := (stOf_inv R.1).1 R.2
  rw [rowsB_one, (gramRow (okRow hw hs (i := r) (by omega)) (rowLt hw hs _) (nextLt hw hs _) R.1.sum).1 h1 hpf]

/-- **An `HPL` field**: `u32 qhk` (as `qhk 0 0 0`). -/
theorem hplField {r : Nat} (hU : UField s r 4) (hst : stOf (s.row r) = 1) (hlt : r + 4 ≤ s.rows.length)
    (hq : ∀ d, d < 4 → s.row (r + d) qb = 1) :
    rowsB s r 4 = [s.row r qhk, 0, 0, 0] := by
  have R := fieldRowSt hw hs hU hst hlt hq
  have G := fun d (hd : d < 4) => gramRow (okRow hw hs (i := r + d) (by omega)) (rowLt hw hs _) (nextLt hw hs _)
    (R d hd).1.sum
  have H := fun d (hd : d < 4) => (stOf_inv (R d hd).1).2.1 (R d hd).2
  have fs0 := (hU.fs 0 (by omega)).2 rfl
  have fs' : ∀ d, d < 4 → d ≠ 0 → s.row (r + d) fs = 0 := fun d hd h0 => by
    rcases rowBool (okRow hw hs (i := r + d) (by omega)) (rowLt hw hs _) (x := fs) (by decide) with h | h
    · exact h
    · exact absurd ((hU.fs d hd).1 h) h0
  have e0 := (G 0 (by omega)).2.1 (H 0 (by omega)) (by simpa using fs0)
  have e1 := (G 1 (by omega)).2.2 (H 1 (by omega)) (fs' 1 (by omega) (by omega))
  have e2 := (G 2 (by omega)).2.2 (H 2 (by omega)) (fs' 2 (by omega) (by omega))
  have e3 := (G 3 (by omega)).2.2 (H 3 (by omega)) (fs' 3 (by omega) (by omega))
  simp only [Nat.add_zero] at e0
  rw [rowsB_four, e0, e1, e2, e3]

end

end ZkFormal.NearV3.UpsRows
