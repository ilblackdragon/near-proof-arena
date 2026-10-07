import ZkFormal.NearV3.Rcpt.Extract.V.BoundaryTraffic

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Two distinguished rows contribute once each, with every intervening row silent. -/
theorem flatMap_two_rows {α : Type} (f : Nat→List α) (s T j : Nat)
    (hj : 0<j) (hT : j<T) (hz : ∀ k,k<T → k≠0 → k≠j → f (s+k)=[]) :
    (List.range' s T).flatMap f=f s++f (s+j) := by
  have hw := flatMap_window f s T 0 (j+1) (by omega)
    (by intro k hk ho; exact hz k hk (by omega) (by omega))
  rw [hw,Nat.add_zero,show j+1=1+(j-1)+1 by omega,
    ←List.range'_append_1,←List.range'_append_1,List.flatMap_append,List.flatMap_append]
  have hm : (List.range' (s+1) (j-1)).flatMap f=[] := by
    apply flatMap_range'_nil
    intro k hk
    rw [show s+1+k=s+(1+k) by omega]
    exact hz (1+k) (by omega) (by omega) (by omega)
  rw [hm]
  simp only [List.range'_one,List.flatMap_singleton,List.append_nil,show s+(1+(j-1))=s+j by omega]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem final_gate {q : Nat} (hq : q<tr.height tt) :
    tr.cell tt q gF=tr.cell tt q rf+tr.cell tt q ee*tr.cell tt q sT0 := by
  have hh := con hL hq (e:=sub (c gF) (.add (c rf) (.mul (c ee) (c sT0)))) (mem_ky (by simp [cKey]))
  simp only [eval_sub,eval_add,eval_mul,eval_c] at hh
  grind

/-- No final-result lookup is permitted outside receipt/access starts. -/
theorem final_silent {q : Nat} (hq : q<tr.height tt)
    (hp : tr.cell tt q sPL=0) (ht : tr.cell tt q sT0=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_FINAL false=[] := by
  have hr : tr.cell tt q rf=0 := by
    apply bool01 hL hq (by simp [boolCols])
    intro h1
    have hh := (bounds hL hq).2.1 h1
    rw [hp] at hh
    exact fp_zero_ne_one hh.1
  rw [rowT_final]
  have hg := final_gate hL hq
  rw [hr,ht] at hg
  exact gt_zero (by change tr.cell tt q gF=0; grind) _

theorem ListBlockWf.header_final {B : ListBlock} (h : ListBlockWf tr tt B) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_FINAL false)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  have ho := (oneHot hL (r:=B.start+k) (by omega) (by simp [states]) hs).2
  exact final_silent hL (by omega) (ho sPL (by simp [states]) (by decide))
    (ho sT0 (by simp [states]) (by decide))

/-- The complete receipt interval contributes only the account and access-key result rows. -/
theorem Layout.final_rows {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_FINAL false)=
      rowTraffic RcptV3.interactions tr tt y.s pub B_FINAL false++
      rowTraffic RcptV3.interactions tr tt (y.s+(40+y.Lp+y.Lv)) pub B_FINAL false := by
  have hm : (sT0,40+y.Lp+y.Lv,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hl
  apply flatMap_two_rows _ y.s y.tot (40+y.Lp+y.Lv) (by omega) (by exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hl)
  intro k hk h0 ht
  rw [rowT_final]
  have hr := (h.start_flags hL).2.2
  have hg := gF_row hL h (rN:=cv tr tt y.s RcptV3.r) (Fp.ofNat_toNat _).symm hr k hk
  rw [if_neg h0,if_neg (by simpa only [t0Off] using ht)] at hg
  exact gt_zero (by change tr.cell tt (y.s+k) gF=0; grind) _

end ZkFormal.NearV3.RcptV3Proof
