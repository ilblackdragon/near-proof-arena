import ZkFormal.NearV3.Render.Ups.CompactExtract.RbiBytes
import ZkFormal.NearV3.Extract.Ups.MvRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem nibBits (hst : C sTAG+C sHPL+C sHPF=1) : ∀ i,i<8 → C (reg i)≤1 :=
  headerBits ok hC hst

/-- The `TAG` read of a moved-key part: the source's first byte, `hi = 2·qtl + podd`. -/
theorem mvTag (hoh : OneHot C) (hT : C sTAG = 1) (hk : C kMVL + C kMVE = 1) (hx : C xcp = 0)
    (hqt : C qtl ≤ 1) (hpo : C podd ≤ 1) :
    C (reg 0) + 2 * C (reg 1) + 4 * C (reg 2) + 8 * C (reg 3) = 2 * C qtl + C podd ∧
    C rb = 16 * (C (reg 0) + 2 * C (reg 1) + 4 * C (reg 2) + 8 * C (reg 3)) +
      (C (reg 4) + 2 * C (reg 5) + 4 * C (reg 6) + 8 * C (reg 7)) := by
  have bt := nibBits ok hC hD (by have := hoh.sum; have := hoh.bs; omega)
  have b0 := bt 0 (by omega); have b1 := bt 1 (by omega); have b2 := bt 2 (by omega); have b3 := bt 3 (by omega)
  have b4 := bt 4 (by omega); have b5 := bt 5 (by omega); have b6 := bt 6 (by omega); have b7 := bt 7 (by omega)
  have f1 := rTAG ok hC hoh.sum hT
  have f2 := rTAGh ok hC hoh.sum hT
  have hk' : ((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp) + ((C xcp : Nat) : Fp) = 1 := by
    rw [hx, ← natCast_add, ← natCast_add, show C kMVL + C kMVE + 0 = 1 by omega]; rfl
  rw [hk'] at f1 f2
  simp only [hb, lb, Nat.pow_zero, Nat.pow_succ] at f1 f2
  refine ⟨?_, ?_⟩
  · apply natv (by rw [P_lit]; omega) (by rw [P_lit]; omega)
    simp only [natCast_add, natCast_mul]
    grind
  · apply natv (hC _) (by rw [P_lit]; omega)
    simp only [natCast_add, natCast_mul]
    grind

/-- The `HPF` byte of a moved-key part. -/
theorem mvHpf (hoh : OneHot C) (hh : C sHPF = 1) (hk : C kMVL + C kMVE = 1) (hqt : C qtl ≤ 1) (hqo : C qodd ≤ 1) :
    C rb = 16 * (C (reg 0) + 2 * C (reg 1) + 4 * C (reg 2) + 8 * C (reg 3)) +
      (C (reg 4) + 2 * C (reg 5) + 4 * C (reg 6) + 8 * C (reg 7)) ∧
    C b = 32 * C qtl + 16 * C qodd + C qodd * (C (reg 4) + 2 * C (reg 5) + 4 * C (reg 6) + 8 * C (reg 7)) := by
  have bt := nibBits ok hC hD (by have := hoh.sum; have := hoh.bs; omega)
  have b0 := bt 0 (by omega); have b1 := bt 1 (by omega); have b2 := bt 2 (by omega); have b3 := bt 3 (by omega)
  have b4 := bt 4 (by omega); have b5 := bt 5 (by omega); have b6 := bt 6 (by omega); have b7 := bt 7 (by omega)
  have f1 := rHPF ok hC hoh.sum hh
  have f2 := bHPFm ok hC hoh.sum hh
  have hk' : ((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp) = 1 := by
    rw [← natCast_add, show C kMVL + C kMVE = 1 by omega]; rfl
  rw [hk'] at f1 f2
  simp only [hb, lb, Nat.pow_zero, Nat.pow_succ] at f1 f2
  refine ⟨?_, ?_⟩
  · apply natv (hC _) (by rw [P_lit]; omega)
    simp only [natCast_add, natCast_mul]
    grind
  · have hlo : C (reg 4) + 2 * C (reg 5) + 4 * C (reg 6) + 8 * C (reg 7) < 16 := by omega
    apply natv (hC _) (by
      rw [P_lit]
      have : C qodd * (C (reg 4) + 2 * C (reg 5) + 4 * C (reg 6) + 8 * C (reg 7)) ≤ 15 := by
        rcases (show C qodd = 0 ∨ C qodd = 1 by omega) with h | h <;> rw [h] <;> omega
      omega)
    simp only [natCast_add, natCast_mul]
    grind

/-- Read positions of a moved-key part after its `HPL` field. -/
theorem mvPos (hoh : OneHot C) (hrd : C rd = 1) (hk : C kMVL + C kMVE = 1)
    (hs : C sHPF + C sKEY + C sVLEN + C sVH + C sCH = 1) (hle : C qhk ≤ C qpos + C phk) (hlt : C qpos + C phk < P) :
    C spos = C qpos + C phk - C qhk := by
  have hk' : ((C kMVL : Nat) : Fp) + ((C kMVE : Nat) : Fp) = 1 := by
    rw [← natCast_add, show C kMVL + C kMVE = 1 by omega]; rfl
  have hb := hoh.bs
  have f : ((C spos : Nat) : Fp) + ((C qhk : Nat) : Fp) - (((C qpos : Nat) : Fp) + ((C phk : Nat) : Fp)) = 0 := by
    rcases (show C sHPF = 1 ∨ C sKEY = 1 ∨ C sVLEN = 1 ∨ C sVH = 1 ∨ C sCH = 1 by omega) with h | h | h | h | h
    · have := pMKHPF ok hC hoh.sum hrd h; rw [hk'] at this; grind
    · have := pMKKEY ok hC hoh.sum hrd h; rw [hk'] at this; grind
    · have := pMKVLEN ok hC hoh.sum hrd h; rw [hk'] at this; grind
    · have := pMKVH ok hC hoh.sum hrd h; rw [hk'] at this; grind
    · have := pMKCH ok hC hoh.sum hrd h; rw [hk'] at this; grind
  exact sub_of_cast (hC _) hlt hle (by rw [natCast_add]; grind)

/-- The new hex-prefix length of a moved key. -/
theorem mvQhk (hpf : C pf = 1) (hk : C kMVL + C kMVE = 1) {I : Nat} (hI : C ti1 + 2 * C ti2 = I) (hI3 : I < 3)
    (hq : C qhk < 2 ^ 23) (hp : C phk < 2 ^ 23) (hqo : C qodd ≤ 1) (hpo : C podd ≤ 1) :
    2 * C qhk + C qodd + I + 1 = 2 * C phk + C podd := by
  have f := factN ok hC hD (e := .mul (c pf) (.mul kM (sub (.add (smul 2 (c qhk)) (c qodd))
      (sub (.add (smul 2 (c phk)) (c podd)) (.add tIE (Dsl.k 1)))))) (memPlan (by simp [cPlan]))
  have := hC kMVL; have := hC kMVE; have := hC ti1; have := hC ti2
  simp only [kM, tIE, P_lit] at *
  nev_simp at f
  rw [hpf, show (C kMVL + C kMVE) % 2013265921 = 1 by omega,
    show (C ti1 + 2 * C ti2 % 2013265921) % 2013265921 = I by omega] at f
  simp at f
  omega

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
