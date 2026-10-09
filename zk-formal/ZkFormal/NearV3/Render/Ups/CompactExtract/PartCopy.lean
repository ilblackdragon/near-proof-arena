import ZkFormal.NearV3.Render.Ups.CompactExtract.PartFresh
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
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
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
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


end ZkFormal.NearV3.Render.UpsRelay.Extract
