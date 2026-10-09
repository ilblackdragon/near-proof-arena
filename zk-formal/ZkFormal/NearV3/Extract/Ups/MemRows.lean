import ZkFormal.NearV3.Extract.Ups.PlanRows

/-!
# ZkFormal.NearV3.Extract.Ups.MemRows — the `memory_usage` rows, row facts

A `MEM` row (`sMEM = 1`) of a node part: the inside input `X1 = A + B − C`, the outside
input `Ein`, the carry-ins (`0` on the first row, the previous carry-outs otherwise), the two
chain equations and the exact limb `rx` sent on `MEMD` (`memRow`), as natural-number facts
modulo `P` on the cells; `t` (8 bits), `cb`, `cc` (3 bits each) are the bit registers.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Bit registers of a `MEM` row: `t` (8 bits), inside carry `cb`, outside carry `cc`. -/
def tvOf (C : URow) : Nat := ((List.range 8).map fun i => 2 ^ i * C (reg i)).sum
def cbOf (C : URow) : Nat := bitsVal (fun i => C (cb i)) 0 17
def ccOf (C : URow) : Nat := bitsVal (fun i => C (cc i)) 0 16

/-- The facts of a `MEM` row (cells as naturals below `P`; `P` written out for `omega`). -/
structure MemRowF (C D : URow) : Prop where
  tv : tvOf C < 256
  cb : cbOf C < 131072
  cc : ccOf C < 65536
  /-- inside input `X1 ≡ A + B − C` -/
  x1 : (C X1 + (C cO * C mCv + C cS * C (SR 0) + C fs * C Cc)) % 2013265921 =
    (C useA * C rb + C bN * C mBv + C bL * C (LR 0)) % 2013265921
  /-- outside input -/
  ein : C Ein = (C fs * C Kc + C eL * C (LR 0) + C eS * C (SR 0)) % 2013265921
  /-- carry-ins: `0` on the first row -/
  ci0 : C fs = 1 → C ci = 0 ∧ C ci2 = 0
  /-- carry-ins of the next row: `cb − 3` and `cc` -/
  ciN : C fe = 0 → (D ci + 65536) % 2013265921 = cbOf C ∧ D ci2 = ccOf C
  /-- chain 1: `σ·X1 + ci = t + 256·co` (`co = cb − 3`, or `cb` on the last row) -/
  ch1 : (C neg = 0 → (C X1 + C ci + 16777216 * (1 - C fe)) % 2013265921 = (tvOf C + 256 * cbOf C) % 2013265921) ∧
    (C neg = 1 → (C ci + 16777216 * (1 - C fe)) % 2013265921 = (C X1 + tvOf C + 256 * cbOf C) % 2013265921)
  /-- chain 2: `Ein + (1 − neg)·t + ci2 = b + 256·cc` -/
  ch2 : (C Ein + (1 - C neg) * tvOf C + C ci2) % 2013265921 = (C b + 256 * ccOf C) % 2013265921
  /-- the exact limb -/
  rx : C rx = (C b + 256 * (C fe * ((1 - C neg) * cbOf C + ccOf C))) % 2013265921

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem memBits (hm : C sMEM=1) : ∀ x∈memBitCols,C x≤1 := by
  intro x hx
  have h := fact ok (e:=Expr.mul (c sMEM) (Dsl.bool (c x))) (memBool (by
    unfold cBool
    simp only [List.mem_append,List.mem_map,List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨x,hx,rfl⟩))))
  uev_simp
  simp only [hm] at h
  have e : Fp.ofNat 1=1 := rfl
  rw [e] at h
  exact le1 (nat01 (hC _) (by grind))

/-- **A `MEM` row.** -/
theorem memRow (hm : C sMEM = 1) (hneg : C neg ≤ 1) (hfe : C fe ≤ 1) : MemRowF C D := by
  have bt := memBits ok hC hD hm
  have ht : ∀ i,i<8 → C (tb i)≤1 := by
    intro i hi
    exact bt _ (by simp only [memBitCols,List.mem_append,List.mem_map,List.mem_range]; exact Or.inl (Or.inl ⟨i,hi,rfl⟩))
  have hb : ∀ i,i<17 → C (cb i)≤1 := by
    intro i hi
    exact bt _ (by simp only [memBitCols,List.mem_append,List.mem_map,List.mem_range]; exact Or.inl (Or.inr ⟨i,hi,rfl⟩))
  have hc : ∀ i,i<16 → C (cc i)≤1 := by
    intro i hi
    exact bt _ (by simp only [memBitCols,List.mem_append,List.mem_map,List.mem_range]; exact Or.inr ⟨i,hi,rfl⟩)
  have hcb : cbOf C<131072 := bitsVal_lt _ 0 17 (by simpa using hb)
  have hcc : ccOf C<65536 := bitsVal_lt _ 0 16 (by simpa using hc)
  have b0 := ht 0 (by omega); have b1 := ht 1 (by omega); have b2 := ht 2 (by omega); have b3 := ht 3 (by omega)
  have b4 := ht 4 (by omega); have b5 := ht 5 (by omega); have b6 := ht 6 (by omega); have b7 := ht 7 (by omega)
  have htv : tvOf C<256 := by
    simp only [tvOf,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
      List.nil_append,List.cons_append,List.sum_cons,List.sum_nil]
    simp only [tb] at b0 b1 b2 b3 b4 b5 b6 b7
    omega
  have eT : nev C D tE=tvOf C := by
    simp only [tvOf,tE,Dsl.bits,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
      List.nil_append,List.cons_append,List.sum_cons,List.sum_nil]
    nev_simp
    simp only [tb]
    simp
    simp only [tb] at b0 b1 b2 b3 b4 b5 b6 b7
    omega
  have eB : nev C D cbE=cbOf C := by
    have h := hcb
    simp only [cbOf,bitsVal] at h
    simp only [cbOf,bitsVal,cbE,Dsl.bits,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
      List.nil_append,List.cons_append]
    nev_simp
    simp [cb] at h ⊢
    omega
  have eC : nev C D ccE=ccOf C := by
    have h := hcc
    simp only [ccOf,bitsVal] at h
    simp only [ccOf,bitsVal,ccE,Dsl.bits,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
      List.nil_append,List.cons_append]
    nev_simp
    simp [cc] at h ⊢
    omega
  have f1 := factN ok hC hD (e := .mul (c sMEM) (sub (c X1) (sub (sum [.mul (c useA) (c rb), .mul (c bN) (c mBv),
      .mul (c bL) (c (LR 0))]) (sum [.mul (c cO) (c mCv), .mul (c cS) (c (SR 0)), .mul (c fs) (c Cc)]))))
    (memMem (by simp [cMem]))
  have f2 := factN ok hC hD (e := .mul (c sMEM) (sub (c Ein) (sum [.mul (c fs) (c Kc), .mul (c eL) (c (LR 0)),
      .mul (c eS) (c (SR 0))]))) (memMem (by simp [cMem]))
  have f3 := factN ok hC hD (e := mul3 (c sMEM) (c fs) (c ci)) (memMem (by simp [cMem]))
  have f4 := factN ok hC hD (e := mul3 (c sMEM) (c fs) (c ci2)) (memMem (by simp [cMem]))
  have f5 := factN ok hC hD (e := .mul (.mul (c sMEM) (not (c fe))) (sub (n ci) coE)) (memMem (by simp [cMem]))
  have f6 := factN ok hC hD (e := .mul (.mul (c sMEM) (not (c fe))) (sub (n ci2) ccE)) (memMem (by simp [cMem]))
  have f7 := factN ok hC hD (e := .mul (c sMEM) (sub (.add (.mul sigE (c X1)) (c ci)) (.add tE (smul 256 coE))))
    (memMem (by simp [cMem]))
  have f8 := factN ok hC hD (e := .mul (c sMEM) (sub (sum [c Ein, .mul (not (c neg)) tE, c ci2]) (.add (c b) (smul 256 ccE))))
    (memMem (by simp [cMem]))
  have f9 := factN ok hC hD (e := .mul (c sMEM) (sub (c rx) (.add (c b) (smul 256 (.mul (c fe)
      (.add (.mul (not (c neg)) cbE) ccE)))))) (memMem (by simp [cMem]))
  simp only [coE, sigE] at f5 f7
  nev_simp at f1 f2 f3 f4 f5 f6 f7 f8 f9
  simp only [eT, eB, eC, hm, Nat.one_mul] at f1 f2 f3 f4 f5 f6 f7 f8 f9
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d
  have := a X1; have := a Ein; have := a ci; have := a ci2; have := a rx; have := a b; have := d ci; have := d ci2
  have := a fs; have := a useA; have := a rb; have := a bN; have := a mBv; have := a bL; have := a (LR 0)
  have := a cO; have := a mCv; have := a cS; have := a (SR 0); have := a Cc; have := a Kc; have := a eL; have := a eS
  refine ⟨htv, hcb, hcc, ?_, ?_, fun h => ?_, fun h => ?_, ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · omega
  · omega
  · simp [h] at f3 f4; omega
  · simp [h] at f5 f6; omega
  · rcases (show C fe = 0 ∨ C fe = 1 by omega) with h' | h' <;> simp [h, h'] at f7 ⊢ <;> omega
  · rcases (show C fe = 0 ∨ C fe = 1 by omega) with h' | h' <;> simp [h, h'] at f7 ⊢ <;> omega
  · rcases (show C neg = 0 ∨ C neg = 1 by omega) with h' | h' <;> simp [h'] at f8 ⊢ <;> omega
  · rcases (show C neg = 0 ∨ C neg = 1 by omega) with h' | h' <;>
    rcases (show C fe = 0 ∨ C fe = 1 by omega) with h'' | h'' <;> simp [h', h''] at f9 ⊢ <;> omega

end

end ZkFormal.NearV3.UpsRows
