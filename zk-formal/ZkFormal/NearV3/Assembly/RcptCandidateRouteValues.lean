import ZkFormal.NearV3.Assembly.RcptCandidateCharClass
import ZkFormal.NearV3.Assembly.RcptCandidateRouteCompare
-- Source RouteValues.lean SHA256: b2badefefcf7c11581fe6ed458ed587fda37a4502dd568fbdbcc0f11eec2a927.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.RouteCompare

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
variable (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
include hL lay

/-- Routing's byte column is the receiver byte or the canonical zero end marker. -/
theorem route_value (k : Nat) (hk : k≤y.Lv) :
    cv tr tt (lkRow y k) vB=padB (rcptOf tr tt y).v k := by
  have hq := route_height hL lay k hk
  by_cases he : k=y.Lv
  · subst k
    have F := route_end hL lay
    have hs : tr.cell tt (lkRow y y.Lv) sRID=1 := by simpa using F.fld.st 0 (by decide)
    have hf : tr.cell tt (lkRow y y.Lv) fs=1 := by simpa using F.fld.fs 0 (by decide)
    have cc := con hL hq (e:=mul3 (c sRID) (c fs) (c vB)) (mem_ro (by simp [cRoute]))
    simp only [eval_mul3,eval_c,hs,hf] at cc
    have hv : tr.cell tt (lkRow y y.Lv) vB=0 := by grind
    simp [cv,hv,Fp.toNat_zero,padB,rcptOf,colAt,List.getD]
  · have F := route_receiver hL lay
    have hs : tr.cell tt (lkRow y k) sV=1 := by simpa [lkRow] using F.fld.st k (by omega)
    have cc := con hL hq (e:=.mul (c sV) (sub (c vB) (c b))) (mem_ro (by simp [cRoute]))
    simp only [eval_mul,eval_c,eval_sub,hs] at cc
    have hv : tr.cell tt (lkRow y k) vB=tr.cell tt (lkRow y k) b := by grind
    have hk' : k<y.Lv := by omega
    simpa [cv,padB,rcptOf,colAt,List.getD,hk',lkRow] using congrArg Fp.toNat hv

/-- The receiver bytes are positive native bytes, as needed by padded lexicographic comparison. -/
theorem route_receiver_bytes : ∀ a∈(rcptOf tr tt y).v,0<a ∧ a<256 := by
  intro a ha
  change a∈colAt tr tt (y.s+(8+y.Lp)) y.Lv b at ha
  simp only [colAt,List.mem_map,List.mem_range] at ha
  obtain ⟨k,hk,rfl⟩ := ha
  have F := route_receiver hL lay
  have hs : tr.cell tt (lkRow y k) sV=1 := by simpa [lkRow] using F.fld.st k hk
  have hq := route_height hL lay k (by omega)
  obtain ⟨hv,hl,hh,_,_⟩ := char_val hL hq (by simp) hs
  have hc := (char_class hL hq (by simp) hs).1
  have hh2 : 2≤hiV tr tt (lkRow y k) := by unfold ClassOK at hc; omega
  change 0<cv tr tt (lkRow y k) b ∧ cv tr tt (lkRow y k) b<256
  omega

/-- A selected physical row contributes its precise public-boundary lookup record. -/
theorem route_record (k : Nat) (hk : k≤y.Lv) (hg : tr.cell tt (lkRow y k) gBd=1) :
    (k,cv tr tt (lkRow y k) loB,cv tr tt (lkRow y k) hiB,cv tr tt (lkRow y k) hnB,cv tr tt (lkRow y k) uB)∈(rcptOf tr tt y).rlk := by
  apply List.mem_filterMap.mpr
  exact ⟨k,List.mem_range.mpr (by omega),by simp [hg]⟩

/-- The final upper comparison must be strict if its prefix remains equal. -/
theorem route_upper_end (he : tr.cell tt (lkRow y y.Lv) eqH=1) :
    tr.cell tt (lkRow y y.Lv) eH=0 := by
  have F := route_end hL lay
  have hs : tr.cell tt (lkRow y y.Lv) sRID=1 := by simpa using F.fld.st 0 (by decide)
  have hf : tr.cell tt (lkRow y y.Lv) fs=1 := by simpa using F.fld.fs 0 (by decide)
  have cc := con hL (route_height hL lay y.Lv (by omega))
    (e:=.mul (mul3 (c sRID) (c fs) (c eqH)) (c eH)) (mem_ro (by simp [cRoute]))
  simp only [eval_mul,eval_mul3,eval_c,hs,hf,he] at cc
  grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
