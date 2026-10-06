import ZkFormal.NearV3.Extract.Ups.NlfBytes

/-!
# ZkFormal.NearV3.Extract.Ups.PartK — generic per-part byte facts (layer 2)

The pieces shared by the per-kind byte statements:

* `PartK s o ℓ …`: the row facts of a part `(o, ℓ)` with indices (`partK`);
* `rdCopy`: a copied byte is read (`rd = 1`) unless an extra read applies to the row;
* `copyRun`: rows that copy with `spos = δ + d` emit the source bytes `Pb[δ …]`;
* fresh fields: `vlenFresh` (`L0 L1 L2 0`), `vhFresh` (the `DIGEST` register at the value id
  and length `L`);
* the `L` register on the `MEM` field (`memL`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Row facts of a part `(o, ℓ)` with indices. -/
structure PartK (s : UpsSeg) (o ℓ ci ti di si ki sdi : Nat) : Prop where
  pos : 0 < ℓ
  le : o + ℓ ≤ s.rows.length
  qb : ∀ d, d < ℓ → s.row (o + d) qb = 1
  pf : s.row o pf = 1
  pc : ∀ d, d < ℓ → ∀ x ∈ partConst, s.row (o + d) x = s.row o x
  ix : ∀ d, d < ℓ → IxOf (s.row (o + d)) ci ti di si ki sdi
  sel : ∀ d, d < ℓ → s.row (o + d) vcp = vcpV ci ki ∧ s.row (o + d) xcp = xcpV ci ki ∧
    s.row (o + d) ba0 = ba0V si ki ∧ s.row (o + d) ba1 = ba1V si ki ∧
    s.row (o + d) spY1 = spY1V ci si ki ∧ s.row (o + d) spY2 = spY2V ci si ki
  idx : ci < 11 ∧ ti < 3 ∧ di < 3 ∧ si < 3 ∧ ki < 12 ∧ sdi < 3

/-- The list `[Pb[δ], …, Pb[δ+n−1]]` is a slice. -/
theorem map_getD_slice (Pb : List Nat) (δ n : Nat) (h : δ + n ≤ Pb.length) :
    (List.range n).map (fun d => Pb.getD (δ + d) 0) = (Pb.drop δ).take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show δ + i < Pb.length by omega)]

theorem slice_append_left {A B : List Nat} {δ n : Nat} (h : δ + n ≤ A.length) :
    ((A ++ B).drop δ).take n = (A.drop δ).take n := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem slice_append_right {A B : List Nat} {δ n : Nat} (h : A.length ≤ δ) :
    ((A ++ B).drop δ).take n = (B.drop (δ - A.length)).take n := by
  obtain ⟨e, rfl⟩ : ∃ e, δ = A.length + e := ⟨δ - A.length, by omega⟩
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- **A copied byte is read** when no extra read applies to the row. -/
theorem rdCopy (hq : C qb = 1) (hcp : C cp = 1) (hoh : OneHot C)
    (h1 : C sTAG = 1 → C kRBV = 0 ∧ C kMVL = 0 ∧ C kMVE = 0 ∧ C xcp = 0)
    (h2 : C sHPL + C sHPF = 1 → C kMVL = 0 ∧ C kMVE = 0)
    (h4 : C sVLEN = 1 → C kRBR = 0) (h5 : C sBM = 1 → C xcp = 0) (h7 : C rdc = 0) : C rd = 1 := by
  have f := factN ok hC hD (e := .mul (c qb) (sub (c rd) (.add (c cp) (sum [
    .mul (c sTAG) (sumc [kRBV, kMVL, kMVE, xcp]),
    mul3 (c sHPL) (c fs) kM, .mul (c sHPF) kM, .mul (c sVLEN) (c kRBR),
    mul3 (c sBM) (c fs) (c xcp), .mul (c sMEM) (not (c kNLF)), c rdc])))) (memBytes (by simp [cBytes]))
  have fm := factN ok hC hD (e := .mul (c sMEM) (c cp)) (memBytes (by simp [cBytes]))
  have hS := hoh.sum
  have hb := hoh.bs
  have := hC rd
  simp only [P_lit] at this
  simp only [sumc, kM, List.map_cons, List.map_nil] at f
  nev_simp at f fm
  rw [hq, hcp, h7] at f
  rw [hcp] at fm
  have hcase : C sTAG = 1 ∨ C sHPL = 1 ∨ C sHPF = 1 ∨ C sKEY = 1 ∨ C sVLEN = 1 ∨ C sVH = 1 ∨ C sBM = 1 ∨
      C sCH = 1 ∨ C sMEM = 1 := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h
  · obtain ⟨a1, a2, a3, a4⟩ := h1 h
    have z : C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, a1, a2, a3, a4, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1,
      z.2.2.2.2.2.2.2] at f
    omega
  · obtain ⟨a1, a2⟩ := h2 (by omega)
    have z : C sTAG = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, a1, a2, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1,
      z.2.2.2.2.2.2.2] at f
    omega
  · obtain ⟨a1, a2⟩ := h2 (by omega)
    have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, a1, a2, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1,
      z.2.2.2.2.2.2.2] at f
    omega
  · have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2] at f
    omega
  · have a1 := h4 h
    have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, a1, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2] at f
    omega
  · have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sBM = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2] at f
    omega
  · have a1 := h5 h
    have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sCH = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, a1, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2] at f
    omega
  · have z : C sTAG = 0 ∧ C sHPL = 0 ∧ C sHPF = 0 ∧ C sKEY = 0 ∧ C sVLEN = 0 ∧ C sVH = 0 ∧ C sBM = 0 ∧ C sMEM = 0 := by
      omega
    simp [h, z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1, z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2] at f
    omega
  · simp [h] at fm

/-- A copied byte (outside a bitmap) is the read byte. -/
theorem bCopyN (hcp : C cp = 1) (hbm : C sBM = 0) : C b = C rb := by
  have f := factN ok hC hD (e := .mul (c cp) (sub (c b) (.add (c rb) (.mul (c sBM) (.add (.mul (c fs) (c ba0))
    (.mul (not (c fs)) (c ba1))))))) (memBytes (by simp [cBytes]))
  nev_simp at f
  have := hC b; have := hC rb
  simp only [P_lit] at *
  simp [hcp, hbm] at f
  omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **Copied rows**: rows `r … r+n−1` that read and copy at `spos = δ + d` emit `Pb[δ …]`
(`Pb` = the post bytes of the source record, by the `UPB` reads `hR`). -/
theorem copyRun (Pb : Nat → List Nat)
    (hR : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0)
    {r n δ N : Nat} (hlt : r + n ≤ s.rows.length) (hδ : δ + n ≤ (Pb N).length)
    (hrows : ∀ d, d < n → s.row (r + d) cp = 1 ∧ s.row (r + d) rd = 1 ∧ s.row (r + d) sBM = 0 ∧
      s.row (r + d) spos = δ + d ∧ s.row (r + d) sN = N) :
    rowsB s r n = ((Pb N).drop δ).take n := by
  rw [← map_getD_slice _ _ _ hδ]
  apply rowsB_eq_map
  intro d hd
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrows d hd
  rw [bCopyN (okRow hw hs (i := r + d) (by omega)) (rowLt hw hs _) (nextLt hw hs _) h1 h3,
    hR (r + d) (by omega) h2, h4, h5]

end

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
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
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v) (hsc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x)
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

end ZkFormal.NearV3.UpsRows

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- The old-length register `SR` shifts on `MEM` rows. -/
theorem memSR (hm : C sMEM = 1) (hfe : C fe = 0) :
    D (SR 0) = C (SR 1) ∧ D (SR 1) = C (SR 2) ∧ D (SR 2) = C (SR 3) ∧ D (SR 3) = 0 := by
  have g0 := factN ok hC hD (e := Expr.mul (.mul (c sMEM) (not (c fe))) (sub (n (SR 0)) (c (SR 1))))
    (memMem (by simp [cMem, List.range_succ]))
  have g1 := factN ok hC hD (e := Expr.mul (.mul (c sMEM) (not (c fe))) (sub (n (SR 1)) (c (SR 2))))
    (memMem (by simp [cMem, List.range_succ]))
  have g2 := factN ok hC hD (e := Expr.mul (.mul (c sMEM) (not (c fe))) (sub (n (SR 2)) (c (SR 3))))
    (memMem (by simp [cMem, List.range_succ]))
  have g3 := factN ok hC hD (e := Expr.mul (.mul (c sMEM) (not (c fe))) (n (SR 3)))
    (memMem (by simp [cMem, List.range_succ]))
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d
  have := a (SR 1); have := a (SR 2); have := a (SR 3); have := d (SR 0); have := d (SR 1); have := d (SR 2)
  have := d (SR 3)
  nev_simp at g0 g1 g2 g3
  simp [hm, hfe] at g0 g1 g2 g3
  omega

end

end ZkFormal.NearV3.UpsRows

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

attribute [local irreducible] UpsSeg.row UpsSeg.next

/-- Byte `j` of a short list (`0` past its end). -/
def bAt (xs : List Nat) (j : Nat) : Nat := xs.getD j 0

theorem bAt_ge (xs : List Nat) (j : Nat) (h : xs.length ≤ j) : bAt xs j = 0 := by
  simp [bAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v) (hsc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x)
  {o ℓ ci ti di si ki sdi : Nat} (K : PartK s o ℓ ci ti di si ki sdi)
include hw hs hsc K

/-- **The `MEM` field's registers**: `fs`, the `L` register (`L0 L1 L2 0 …`) and the old-length
register (`S0 S1 S2 S3 0 …`, its value on the field's first row). -/
theorem memRegs {r0 : Nat} (hU : UField s r0 8) (hst : stOf (s.row r0) = 8) (h1 : o ≤ r0) (h2 : r0 + 8 ≤ o + ℓ) :
    ∀ i, i < 8 → s.row (r0 + i) fs = (if i = 0 then 1 else 0) ∧
      s.row (r0 + i) (LR 0) = bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i ∧
      s.row (r0 + i) (SR 0) = bAt [s.row r0 (SR 0), s.row r0 (SR 1), s.row r0 (SR 2), s.row r0 (SR 3)] i := by
  have F := kField hw hs hsc K hU hst h1 h2
  have hlt : r0 + 8 ≤ s.rows.length := by have := K.le; omega
  have hm : ∀ i, i < 8 → s.row (r0 + i) sMEM = 1 := fun i hi => (stOf_inv (F i hi).1).2.2.2.2.2.2.2.2 (F i hi).2.1
  have fe5 := feZero hw hs hsc K hU hlt
  have ML := fun i (hi : i < 8) => memLR (okRow hw hs (i := r0 + i) (by omega)) (rowLt hw hs _) (nextLt hw hs _) (hm i hi)
  have MS := fun i (hi : i < 7) => memSR (okRow hw hs (i := r0 + i) (by omega)) (rowLt hw hs _) (nextLt hw hs _)
    (hm i (by omega)) (fe5 i (by omega))
  have key : ∀ i, i < 8 →
      (s.row (r0 + i) (LR 0) = bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i ∧
        s.row (r0 + i) (LR 1) = bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] (i + 1) ∧
        s.row (r0 + i) (LR 2) = bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] (i + 2)) ∧
      (s.row (r0 + i) (SR 0) = bAt [s.row r0 (SR 0), s.row r0 (SR 1), s.row r0 (SR 2), s.row r0 (SR 3)] i ∧
        s.row (r0 + i) (SR 1) = bAt [s.row r0 (SR 0), s.row r0 (SR 1), s.row r0 (SR 2), s.row r0 (SR 3)] (i + 1) ∧
        s.row (r0 + i) (SR 2) = bAt [s.row r0 (SR 0), s.row r0 (SR 1), s.row r0 (SR 2), s.row r0 (SR 3)] (i + 2) ∧
        s.row (r0 + i) (SR 3) = bAt [s.row r0 (SR 0), s.row r0 (SR 1), s.row r0 (SR 2), s.row r0 (SR 3)] (i + 3)) := by
    intro i
    induction i with
    | zero =>
      intro _
      have := (ML 0 (by omega)).1 (by simpa using (hU.fs 0 (by omega)).2 rfl)
      simp only [Nat.add_zero] at this ⊢
      have hr : r0 < s.rows.length := by omega
      rw [hsc r0 hr L0 (by decide), hsc r0 hr L1 (by decide), hsc r0 hr L2 (by decide)] at this
      exact ⟨this, rfl, rfl, rfl, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨⟨l0, l1, l2⟩, ⟨s0, s1, s2, s3⟩⟩ := ih (by omega)
      have hL := (ML i (by omega)).2 (fe5 i (by omega))
      have hS := MS i (by omega)
      rw [next_eq hw hs (by omega), show r0 + i + 1 = r0 + (i + 1) by omega] at hL hS
      rw [hL.1, hL.2.1, hL.2.2, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, l1, l2, s1, s2, s3]
      refine ⟨⟨rfl, rfl, ?_⟩, rfl, rfl, rfl, ?_⟩
      · exact (bAt_ge _ _ (by simp)).symm
      · exact (bAt_ge _ _ (by simp)).symm
  intro i hi
  refine ⟨?_, (key i hi).1.1, (key i hi).2.1⟩
  split
  · next h => subst h; simpa using (hU.fs 0 (by omega)).2 rfl
  · next h => exact fsZero hw hs hsc K hU hlt i hi h

/-- **The `MEM` inputs as numbers**: `E = Kc + eL·L + eS·S`, `A = useA·(old memory)`,
`B = bN·new(child) + bL·L`, `C = cO·old(child) + cS·S + Cc` (`S` the old-length register). -/
theorem memIn {r0 : Nat} (hU : UField s r0 8) (hst : stOf (s.row r0) = 8) (h1 : o ≤ r0) (h2 : r0 + 8 ≤ o + ℓ)
    (hb : s.row o eL ≤ 1 ∧ s.row o eS ≤ 1 ∧ s.row o useA ≤ 1 ∧ s.row o bN ≤ 1 ∧ s.row o bL ≤ 1 ∧
      s.row o cO ≤ 1 ∧ s.row o cS ≤ 1) :
    let Lv := s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2
    let Sv := s.row r0 (SR 0) + 256 * s.row r0 (SR 1) + 65536 * s.row r0 (SR 2) + 16777216 * s.row r0 (SR 3)
    limbs (fun i => inE (s.row (r0 + i))) 8 = s.row o Kc + s.row o eL * Lv + s.row o eS * Sv ∧
    limbs (fun i => inA (s.row (r0 + i))) 8 = s.row o useA * limbs (fun i => s.row (r0 + i) rb) 8 ∧
    limbs (fun i => inB (s.row (r0 + i))) 8 = s.row o bN * limbs (fun i => s.row (r0 + i) mBv) 8 + s.row o bL * Lv ∧
    limbs (fun i => inC (s.row (r0 + i))) 8 =
      s.row o cO * limbs (fun i => s.row (r0 + i) mCv) 8 + s.row o cS * Sv + s.row o Cc := by
  intro Lv Sv
  have R := memRegs hw hs hsc K hU hst h1 h2
  have pc := fun i (hi : i < 8) x (hx : x ∈ partConst) => by
    have := K.pc (r0 - o + i) (by omega) x hx; rwa [show o + (r0 - o + i) = r0 + i by omega] at this
  have e : ∀ i, i < 8 → inE (s.row (r0 + i)) = (if i = 0 then s.row o Kc else 0) +
      s.row o eL * bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i +
      s.row o eS * bAt [s.row r0 (SR 0), s.row r0 (SR 1), s.row r0 (SR 2), s.row r0 (SR 3)] i := fun i hi => by
    simp only [inE, (R i hi).1, (R i hi).2.1, (R i hi).2.2, pc i hi Kc (by decide), pc i hi eL (by decide),
      pc i hi eS (by decide)]
    split <;> simp
  have a : ∀ i, i < 8 → inA (s.row (r0 + i)) = s.row o useA * s.row (r0 + i) rb := fun i hi => by
    simp only [inA, pc i hi useA (by decide)]
  have bb : ∀ i, i < 8 → inB (s.row (r0 + i)) = s.row o bN * s.row (r0 + i) mBv +
      s.row o bL * bAt [s.row 0 L0, s.row 0 L1, s.row 0 L2] i := fun i hi => by
    simp only [inB, (R i hi).2.1, pc i hi bN (by decide), pc i hi bL (by decide)]
  have cc : ∀ i, i < 8 → inC (s.row (r0 + i)) = s.row o cO * s.row (r0 + i) mCv +
      s.row o cS * bAt [s.row r0 (SR 0), s.row r0 (SR 1), s.row r0 (SR 2), s.row r0 (SR 3)] i +
      (if i = 0 then s.row o Cc else 0) := fun i hi => by
    simp only [inC, (R i hi).1, (R i hi).2.2, pc i hi cO (by decide), pc i hi cS (by decide), pc i hi Cc (by decide)]
    split <;> simp
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb
  simp only [limbs8]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega), a 0 (by omega), a 1 (by omega), a 2 (by omega), a 3 (by omega), a 4 (by omega),
    a 5 (by omega), a 6 (by omega), a 7 (by omega), bb 0 (by omega), bb 1 (by omega), bb 2 (by omega),
    bb 3 (by omega), bb 4 (by omega), bb 5 (by omega), bb 6 (by omega), bb 7 (by omega), cc 0 (by omega),
    cc 1 (by omega), cc 2 (by omega), cc 3 (by omega), cc 4 (by omega), cc 5 (by omega), cc 6 (by omega),
    cc 7 (by omega)]
  simp only [bAt, List.getD_eq_getElem?_getD, Lv, Sv]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none,
    ite_true, show (1 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega, show (3 : Nat) ≠ 0 by omega,
    show (4 : Nat) ≠ 0 by omega, show (5 : Nat) ≠ 0 by omega, show (6 : Nat) ≠ 0 by omega,
    show (7 : Nat) ≠ 0 by omega, ite_false]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases (show s.row o eL = 0 ∨ s.row o eL = 1 by omega) with h1 | h1 <;>
    rcases (show s.row o eS = 0 ∨ s.row o eS = 1 by omega) with h2 | h2 <;>
    simp only [h1, h2, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add] <;> omega
  · rcases (show s.row o useA = 0 ∨ s.row o useA = 1 by omega) with h3 | h3 <;>
    simp only [h3, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.mul_zero] <;> omega
  · rcases (show s.row o bN = 0 ∨ s.row o bN = 1 by omega) with h4 | h4 <;>
    rcases (show s.row o bL = 0 ∨ s.row o bL = 1 by omega) with h5 | h5 <;>
    simp only [h4, h5, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.mul_zero] <;> omega
  · rcases (show s.row o cO = 0 ∨ s.row o cO = 1 by omega) with h6 | h6 <;>
    rcases (show s.row o cS = 0 ∨ s.row o cS = 1 by omega) with h7 | h7 <;>
    simp only [h6, h7, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.mul_zero] <;> omega

end

end ZkFormal.NearV3.UpsRows
