import ZkFormal.NearV3.Assembly.RcptCandidateIndexedWellformed
-- Source TokenCarry.lean SHA256: b4d9d31591ca3e84175a250a56f18e8f0287752b6d088f9ff55188f39773ec8a.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.IndexedWellformed

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Tokens cross any non-GP row whose successor remains active. -/
theorem token_keep_active {q : Nat} (hq : q+1<tr.height tt)
    (ha : tr.cell tt q act=1) (hn : tr.cell tt (q+1) act=1) (hg : tr.cell tt q sGP=0) :
    ∀ j,j<16 → tr.cell tt (q+1) (tok j)=tr.cell tt q (tok j) := by
  have hh := (le_eq hL hq).2
  rw [hn] at hh
  have hz : tr.cell tt q lastR=0 := by grind
  exact tok_keep hL hq ha hg hz

/-- Tokens are constant across a consecutive active interval with no GP rows. -/
theorem token_span (s n : Nat) (hfin : s+n<tr.height tt)
    (ha : ∀ k,k≤n → tr.cell tt (s+k) act=1)
    (hg : ∀ k,k<n → tr.cell tt (s+k) sGP=0) :
    ∀ j,j<16 → tr.cell tt (s+n) (tok j)=tr.cell tt s (tok j) := by
  induction n with
  | zero => intro j hj; rfl
  | succ n ih =>
    intro j hj
    have hh := token_keep_active hL (q:=s+n) (by omega) (ha n (by omega))
      (by simpa [Nat.add_assoc] using ha (n+1) (by omega)) (hg n (by omega)) j hj
    rw [show s+n+1=s+(n+1) by omega] at hh
    rw [hh,ih (by omega) (fun k hk => ha k (by omega)) (fun k hk => hg k (by omega)) j hj]

/-- Tokens are preserved inside a receipt outside its GP interval, up to an active successor. -/
theorem receipt_token_rows {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (a b : Nat) (hab : a≤b) (hb : b≤y.tot)
    (hgp : ∀ k,a≤k → k<b → k<78+Vt y.Lp y.Lv y.Ls y.kt ∨ 94+Vt y.Lp y.Lv y.Ls y.kt≤k)
    (hend : b=y.tot → tr.cell tt (y.s+y.tot) act=1) :
    ∀ j,j<16 → tr.cell tt (y.s+b) (tok j)=tr.cell tt (y.s+a) (tok j) := by
  have hf := lay.fin
  have hm : (sGP,78+Vt y.Lp y.Lv y.Ls y.kt,16)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hh := token_span hL (y.s+a) (b-a) (by unfold RS.tot at hb; omega) (fun k hk => ?_) (fun k hk => ?_)
  · simpa only [show y.s+a+(b-a)=y.s+b by omega] using hh
  · rw [show y.s+a+k=y.s+(a+k) by omega]
    by_cases he : a+k=y.tot
    · rw [he]
      exact hend (by omega)
    · exact (Layout.row_flags hL lay (a+k) (by omega)).1
  · have hr := cell_state hL lay hm (a+k) (by unfold RS.tot at hb; omega)
    rw [if_neg (by have := hgp (a+k) (by omega) (by omega); omega)] at hr
    simpa only [Nat.add_assoc] using hr

/-- The GP entry token register is the receipt entry token register. -/
theorem token_receipt_start {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    ∀ j,j<16 → tr.cell tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)=tr.cell tt y.s (tok j) := by
  have ht : 94+Vt y.Lp y.Lv y.Ls y.kt<y.tot := by unfold RS.tot total; split <;> omega
  simpa [gq] using receipt_token_rows hL lay 0 (78+Vt y.Lp y.Lv y.Ls y.kt) (by omega) (by omega)
    (fun k hk hk' => Or.inl hk') (fun he => by omega)

/-- After all sixteen GP rows the registers contain the exact generated token bytes. -/
theorem token_receipt_gp_end {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    ∀ j,j<16 → tr.cell tt (y.s+(94+Vt y.Lp y.Lv y.Ls y.kt)) (tok j)=
      ((bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt j) 31 8:Nat):Fp) := by
  intro j hj
  have hh := tok_rot hL lay 16 (by omega) j hj
  rw [if_neg (by omega),show j+16-16=j by omega] at hh
  rw [show gq y.s y.Lp y.Lv y.Ls y.kt 0+16=y.s+(94+Vt y.Lp y.Lv y.Ls y.kt) by unfold gq; omega] at hh
  exact hh

/-- Each receipt's last row retains its exact post-execution token bytes. -/
theorem token_receipt_last {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    ∀ j,j<16 → tr.cell tt (y.s+y.tot-1) (tok j)=
      ((bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt j) 31 8:Nat):Fp) := by
  have ht : 94+Vt y.Lp y.Lv y.Ls y.kt<y.tot := by unfold RS.tot total; split <;> omega
  intro j hj
  have hh := receipt_token_rows hL lay (94+Vt y.Lp y.Lv y.Ls y.kt) (y.tot-1) (by omega) (by omega)
    (fun k hk _ => Or.inr hk) (fun he => by omega) j hj
  rw [show y.s+(y.tot-1)=y.s+y.tot-1 by omega,token_receipt_gp_end hL lay j hj] at hh
  exact hh

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
