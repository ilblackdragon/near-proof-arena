import ZkFormal.NearV3.Render.Ups.CompactExtract.NlfRows
import ZkFormal.NearV3.Render.Ups.CompactExtract.PartFresh
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
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

attribute [local irreducible] UpsSeg.row UpsSeg.next
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v) (hsc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x)
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
      rw [compactNext (s:=s) (by omega), show r0 + i + 1 = r0 + (i + 1) by omega] at hL hS
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

end ZkFormal.NearV3.Render.UpsRelay.Extract
