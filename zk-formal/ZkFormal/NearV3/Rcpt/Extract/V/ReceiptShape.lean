import ZkFormal.NearV3.Rcpt.Extract.V.ViewFacts

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- All V3 receipt vector lengths, including system/routing metadata vectors. -/
theorem lens_of (tr : Trace Fp) (tt : Nat) (y : RS) (hkt : y.kt≤1) :
    let x := rcptOf tr tt y
    x.rid.length=32 ∧ x.pk.length=32+32*x.kt ∧ x.kt≤1 ∧ x.gp.length=16 ∧
    x.dep.length=16 ∧ x.bef.length=16 ∧ x.lk.length=16 ∧ x.st.length=16 ∧
    x.aft.length=16 ∧ x.burnt.length=16 ∧ x.ramt.length=16 ∧ x.rfid.length=32 ∧
    x.peoh.length=32 ∧ x.gv.length=x.v.length ∧ x.gs.length=x.s.length ∧ x.sx.length=x.s.length := by
  obtain ⟨s,h,Lp,Lv,Ls,kt⟩ := y
  simp only at hkt
  cases h <;> simp [rcptOf,colAt_len,hkt]

theorem colAt_lt (tr : Trace Fp) (tt r0 len x : Nat) : ∀ y∈colAt tr tt r0 len x, y<P := by
  intro y hy
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hy
  exact cv_lt _ _ _ _

/-- Lookup metadata read directly from field cells is canonical. -/
theorem small_of (tr : Trace Fp) (tt : Nat) (y : RS) :
    let x := rcptOf tr tt y
    x.kslot<P ∧ x.tprev<P ∧ x.akk<P ∧ x.aku<P ∧ x.q<P := by
  exact ⟨cv_lt _ _ _ _,cv_lt _ _ _ _,cv_lt _ _ _ _,cv_lt _ _ _ _,cv_lt _ _ _ _⟩

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- The reconstructed post-balance bytes are range checked by the active V3 bit constraints. -/
theorem aft8_of {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    Bytes8 (rcptOf tr tt y).aft := by
  have hm : (sDEP,107+Vt y.Lp y.Lv y.Ls y.kt,16)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have he := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hfin := h.fin
  intro v hv
  simp only [rcptOf,List.mem_map,List.mem_range] at hv
  obtain ⟨k,hk,rfl⟩ := hv
  apply bitsVal_lt _ 0 8
  intro i hi
  apply cv_bool
  apply isBool hL (by simp only at he; omega)
  have hmem : xb (0+i)∈(List.range 66).map xb := List.mem_map.mpr ⟨0+i,List.mem_range.mpr (by omega),rfl⟩
  simp only [boolCols,List.mem_append]
  exact Or.inl (Or.inr hmem)

/-- All inherited V1 raw vectors are canonical under the exact V3 layout and constraints. -/
theorem raw_canon_of {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    ∀ v∈(rcptOf tr tt y).raw, v<P := by
  have ha := aft8_of hL h
  have hkt := h.kt1
  intro v hv
  simp only [RcptV.raw,List.mem_append,List.mem_singleton,or_assoc] at hv
  rcases hv with hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv
  all_goals first
    | exact colAt_lt _ _ _ _ _ _ hv
    | (have := ha v hv; unfold P; omega)
    | (subst hv; exact Nat.lt_of_le_of_lt hkt (by decide))
    | skip
  simp only [rcptOf] at hv
  cases he : y.h
  · simp only [he,Bool.false_eq_true,ite_false,List.mem_replicate] at hv
    rw [hv.2]
    decide
  · simp only [he,ite_true] at hv
    exact colAt_lt _ _ _ _ _ _ hv

end ZkFormal.NearV3.RcptV3Proof
