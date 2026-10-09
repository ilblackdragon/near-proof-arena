import ZkFormal.NearV3.Assembly.RcptCandidateReceiptWellformed
-- Source TokenBytes.lean SHA256: c1809644cf06311f3329c57b49264b3ab39ee2ce7738baedb705a1319e65f788.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptWellformed

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The first physical row starts with zero tokens. -/
theorem token_zero (h0 : 0<tr.height tt) (j : Nat) (hj : j<16) : tr.cell tt 0 (tok j)=0 := by
  have cc := con hL h0 (e:=.mul .isFirst (c (tok j))) (mem_rg (by
    unfold cRegs
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩))))))
  simp only [eval_mul,eval_isFirst,eval_c,ite_true] at cc
  grind

/-- Every active physical row has byte-valued token registers, including list headers. -/
theorem token_bytes : ∀ q,q<tr.height tt → tr.cell tt q act=1 → ∀ j,j<16 → cv tr tt q (tok j)<256 := by
  intro q
  induction q with
  | zero =>
    intro hq _ j hj
    simp [cv,token_zero hL hq j hj,Fp.toNat_zero]
  | succ q ih =>
    intro hq ha j hj
    have hpq : q<tr.height tt := by omega
    have hpa : tr.cell tt q act=1 := by
      rcases isBool hL hpq (x:=act) (by simp [boolCols]) with he|he
      · have hh := pad hL hq he
        rw [ha] at hh
        exact False.elim ((by decide : (1:Fp)≠0) hh)
      · exact he
    have hlast : tr.cell tt q lastR=0 := by
      have hh := (le_eq hL hq).2
      rw [ha] at hh
      grind
    rcases isBool hL hpq (x:=sGP) (by simp [boolCols,states]) with hg|hg
    · have hh := tok_keep hL hq hpa hg hlast j hj
      simp only [cv,hh]
      exact ih hpq hpa j hj
    · by_cases hj15 : j<15
      · have cc := con hL hpq (e:=.mul (c sGP) (sub (n (tok j)) (c (tok (j+1))))) (mem_rg (by
          unfold cRegs
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨j,List.mem_range.mpr hj15,rfl⟩)))))
        simp only [eval_mul,eval_sub,eval_c,eval_n,nxt hq,hg] at cc
        have hh : tr.cell tt (q+1) (tok j)=tr.cell tt q (tok (j+1)) := by grind
        simp only [cv,hh]
        exact ih hpq hpa (j+1) (by omega)
      · have hj' : j=15 := by omega
        subst j
        have cc := con hL hpq (e:=.mul (c sGP) (sub (n (tok 15)) (bitsX 31 8))) (mem_rg (by simp [cRegs]))
        obtain ⟨be,bl⟩ := bitsX_eval hL hpq 31 8 (by omega)
        simp only [eval_mul,eval_sub,eval_c,eval_n,nxt hq,hg] at cc
        rw [be] at cc
        have hh : tr.cell tt (q+1) (tok 15)=((bitsVal (fun j => cv tr tt q (xb j)) 31 8:Nat):Fp) := by grind
        rw [cv,hh,toNat_natCast,Nat.mod_eq_of_lt (by unfold P; omega)]
        exact bl

/-- Complete per-receipt Wf extraction with no incoming token-state premise. -/
theorem wf_numbered {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) {rN : Nat}
    (hrN : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hrP : rN<P) (hprovider : (rcptOf tr tt y).tprev≤2^22) :
    (rcptOf tr tt y).Wf rN (pubBytes pub PH_GP 16)
      (sumL (fun j => cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)) 16)
      (sumL (fun k => bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt k) 31 8) 16) := by
  have hh := gp_row hL lay 0 (by decide)
  have ha := (oneHot hL hh.1 (by simp [states]) hh.2.1).1
  exact wf_of hL lay hrN hrP (token_bytes hL _ hh.1 ha) hprovider

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
