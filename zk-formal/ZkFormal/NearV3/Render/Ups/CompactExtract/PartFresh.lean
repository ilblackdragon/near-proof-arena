import ZkFormal.NearV3.Render.Ups.CompactExtract.FieldBytes
import ZkFormal.NearV3.Render.Ups.CompactExtract.Windows
import ZkFormal.NearV3.Extract.Ups.PartK
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) (hD : ∀x,D x<P)
include ok hC hD
theorem gDrow (hq : C qb = 1) (hfs : C fs = 1) (hw3 : C wt3 = 0)
    (hW : (C sVH = 1 ∧ C cp = 0 ∧ C sCH = 0) ∨ (C sCH = 1 ∧ C wfr = 1 ∧ C sVH = 0)) : C gD = 1 := by
  have f := factN ok hC hD (e := sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3))) (memDigest (by simp [cDigest]))
  simp only [winFr] at f
  nev_simp at f
  have := hC gD
  rw [P_lit] at this
  rcases hW with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [hq, hfs, hw3, h1, h2, h3] at f <;> omega

end
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s∈v)
include hw hs
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


theorem qbWt3 {i : Nat} (hi : i<s.rows.length) (hq : s.row i qb=1) : s.row i wt3=0 := by
  obtain ⟨bact,hact,hwk,_,_,_,bw3,_,_,bwk,_⟩:=kinds (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
  rcases bact with h|h <;> rcases bw3 with h'|h' <;> omega

theorem cpZero {i : Nat} (h : ((s.row i cp : Nat):Fp)=((0:Nat):Fp)) : s.row i cp=0 :=
  natv (rowLt hw hs _ _) (by rw [P_lit]; omega) h
end
attribute [local irreducible] UpsSeg.row UpsSeg.next
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **The row facts of part `k`.** -/
theorem partK (k : Nat) (hk : k < ps.length) :
    PartK s ps[k].1 ps[k].2 ci ti di si (kd k) (sdx k) := by
  obtain ⟨i1, i2, i3, i4⟩ := hP.ix
  obtain ⟨k1, k2, -, -⟩ := hP.part k hk
  obtain ⟨-, U⟩ := hL.part k hk
  exact ⟨U.pos, U.le, fun d hd => (U.rows d hd).1, by simpa using (U.rows 0 U.pos).2.2.1.2 rfl,
    fun d hd => (U.rows d hd).2.2.2.2, fun d hd => partIxRow hw hs hL hP k hk d hd,
    fun d hd => partSelAll hw hs hL hP k hk d hd, ⟨i1, i2, i3, i4, k1, k2⟩⟩

end

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v) (hsc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x)
  {o ℓ ci ti di si ki sdi : Nat} (K : PartK s o ℓ ci ti di si ki sdi)
include hw hs hsc K

/-- A field inside the part: its rows are one-hot with the field's state. -/
theorem kField {r n g : Nat} (hU : UField s r n) (hst : stOf (s.row r) = g) (h1 : o ≤ r) (h2 : r + n ≤ o + ℓ) :
    ∀ d, d < n → OneHot (s.row (r + d)) ∧ stOf (s.row (r + d)) = g ∧ r + d < s.rows.length ∧
      IxOf (s.row (r + d)) ci ti di si ki sdi ∧ (∀ x ∈ partConst, s.row (r + d) x = s.row o x) ∧
      s.row (r + d) qb = 1 := by
  have K' := K
  have R := fieldRowSt hw hs hU hst (by have := K.le; omega) (fun d hd => by
    have := K.qb (r - o + d) (by omega); rwa [show o + (r - o + d) = r + d by omega] at this)
  intro d hd
  have e : o + (r - o + d) = r + d := by omega
  refine ⟨(R d hd).1, (R d hd).2, by have := K.le; omega, ?_, ?_, ?_⟩
  · have := K.ix (r - o + d) (by omega); rwa [e] at this
  · have := K.pc (r - o + d) (by omega); rwa [e] at this
  · have := K.qb (r - o + d) (by omega); rwa [e] at this

theorem kSel {r : Nat} (h1 : o ≤ r) (h2 : r < o + ℓ) :
    s.row r vcp = vcpV ci ki ∧ s.row r xcp = xcpV ci ki ∧ s.row r ba0 = ba0V si ki ∧ s.row r ba1 = ba1V si ki ∧
    s.row r spY1 = spY1V ci si ki ∧ s.row r spY2 = spY2V ci si ki := by
  have := K.sel (r - o) (by omega); rwa [show o + (r - o) = r by omega] at this

theorem feZero {r n : Nat} (hU : UField s r n) (hlt : r + n ≤ s.rows.length) : ∀ d, d + 1 < n → s.row (r + d) fe = 0 := by
  intro d hd
  rcases rowBool (okRow hw hs (i := r + d) (by omega)) (rowLt hw hs _) (x := fe) (by decide) with h | h
  · exact h
  · have := (hU.fe d (by omega)).1 h; omega

theorem fsZero {r n : Nat} (hU : UField s r n) (hlt : r + n ≤ s.rows.length) : ∀ d, d < n → d ≠ 0 → s.row (r + d) fs = 0 := by
  intro d hd h0
  rcases rowBool (okRow hw hs (i := r + d) (by omega)) (rowLt hw hs _) (x := fs) (by decide) with h | h
  · exact h
  · exact absurd ((hU.fs d hd).1 h) h0

/-- **A fresh `VLEN` field** (`vcp = 0`): `L0 L1 L2 0`. -/
theorem vlenFresh {r : Nat} (hU : UField s r 4) (hst : stOf (s.row r) = 4) (h1 : o ≤ r) (h2 : r + 4 ≤ o + ℓ)
    (hv : vcpV ci ki = 0) : rowsB s r 4 = [s.row 0 L0, s.row 0 L1, s.row 0 L2, 0] := by
  have F := kField hw hs hsc K hU hst h1 h2
  have cpV : ∀ d, d < 4 → s.row (r + d) sVLEN = 1 ∧ s.row (r + d) cp = 0 := fun d hd => by
    have h1' := (stOf_inv (F d hd).1).2.2.2.2.1 (F d hd).2.1
    refine ⟨h1', cpZero hw hs ?_⟩
    have := cpVLEN (C := s.row (r + d)) (D := s.next (r + d)) (okRow hw hs (F d hd).2.2.1) (rowLt hw hs _)
      (F d hd).1.sum h1'
    rw [this, (kSel hw hs hsc K (r := r + d) (by omega) (by omega)).1, hv]
  have eV := freshVlen hw hs (r0 := r) (by have := K.le; omega) cpV (by simpa using (hU.fs 0 (by omega)).2 rfl)
    (fun d hd => feZero hw hs hsc K hU (by have := K.le; omega) d (by omega))
  have hr : r < s.rows.length := by have := K.le; omega
  rwa [hsc r hr L0 (by decide), hsc r hr L1 (by decide), hsc r hr L2 (by decide)] at eV

/-- **A fresh `VH` field** (`vcp = 0`): the `DIGEST` register of its first row, looked up at the
value id and length `L`. -/
theorem vhFresh {r : Nat} (hU : UField s r 32) (hst : stOf (s.row r) = 5) (h1 : o ≤ r) (h2 : r + 32 ≤ o + ℓ)
    (hv : vcpV ci ki = 0) (hLb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256) :
    rowsB s r 32 = regN (s.row r) ∧ s.row r gD = 1 ∧ s.row r dI = upsIdN (s.row 0 tau) 0 ∧
      s.row r dL = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2 := by
  have F := kField hw hs hsc K hU hst h1 h2
  have hr : r < s.rows.length := by have := K.le; omega
  have cpH : ∀ d, d < 32 → (s.row (r + d) sVH = 1 ∧ s.row (r + d) cp = 0 ∧ s.row (r + d) sCH = 0) ∨
      (s.row (r + d) sCH = 1 ∧ s.row (r + d) wfr = 1 ∧ s.row (r + d) sVH = 0) := fun d hd => by
    have h1' := (stOf_inv (F d hd).1).2.2.2.2.2.1 (F d hd).2.1
    have hs1 := (F d hd).1.sum
    refine Or.inl ⟨h1', cpZero hw hs ?_, by omega⟩
    have := cpVH (C := s.row (r + d)) (D := s.next (r + d)) (okRow hw hs (F d hd).2.2.1) (rowLt hw hs _)
      (F d hd).1.sum h1'
    rw [this, (kSel hw hs hsc K (r := r + d) (by omega) (by omega)).1, hv]
  have eW := freshWin hw hs (r0 := r) (by have := K.le; omega) cpH
    (fun d hd => feZero hw hs hsc K hU (by have := K.le; omega) d (by omega))
  have F0 := F 0 (by omega)
  simp only [Nat.add_zero] at F0
  have hvh : s.row r sVH = 1 := (stOf_inv F0.1).2.2.2.2.2.1 F0.2.1
  have hgD := gDrow (okRow hw hs hr) (rowLt hw hs _) (nextLt hw hs _) F0.2.2.2.2.2 (by simpa using (hU.fs 0 (by omega)).2 rfl)
    (qbWt3 hw hs hr F0.2.2.2.2.2) (by simpa using cpH 0 (by omega))
  have hdI := dI_nat (rowLt hw hs _ _) (dVH (okRow hw hs hr) (rowLt hw hs _) F0.1.sum hgD hvh)
  have hdL := dVHl (okRow hw hs hr) (rowLt hw hs _) F0.1.sum hgD hvh
  rw [hsc r hr tau (by decide)] at hdI
  rw [hsc r hr L0 (by decide), hsc r hr L1 (by decide), hsc r hr L2 (by decide)] at hdL
  refine ⟨eW, hgD, hdI, ?_⟩
  obtain ⟨a0, a1, a2⟩ := hLb
  exact natv (rowLt hw hs _ _) (by rw [P_lit]; omega)
    (by rw [hdL, natCast_add, natCast_add, natCast_mul, natCast_mul]; grind)

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
