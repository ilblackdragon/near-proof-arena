import ZkFormal.NearV3.Assembly.RcptCandidatePublicAlias
-- Source TokenPublic.lean SHA256: edbf04a78750de0552febdd684412d2de4a661e1b35ac6461169a72bceda3f2e.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.TokenSequence
import ZkFormal.NearV3.Rcpt.Extract.V.PublicAlias

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL leN'_rows sumL_congr)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The last extracted active row is exactly the public-total binding row. -/
theorem ListChain.last_row {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    e>0 ∧ e<tr.height tt ∧ tr.cell tt (e-1) lastR=1 := by
  induction h with
  | @last B hw hpad =>
    have hb := hw.bound
    have hl := ListBlockWf.terminal_le hL hw
    have he := (le_eq hL (r:=B.stop-1) (by omega)).2
    rw [show B.stop-1+1=B.stop by omega,hpad,hl] at he
    exact ⟨by omega,hb.2,by grind⟩
  | cons hw ht ih => exact ih

/-- All sixteen terminal token registers bind bytewise to the public burnt total. -/
theorem ListChain.final_token_bytes {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    ∀ j,j<16 → tr.cell tt (e-1) (tok j)=pub.getD (PH_BURNT+j) 0 := by
  obtain ⟨he,hH,hl⟩ := ListChain.last_row hL h
  intro j hj
  have cc := con hL (r:=e-1) (by omega)
    (e:=.mul (c lastR) (sub (c (tok j)) (.pub (PH_BURNT+j)))) (mem_en (by
      unfold cEnd
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩))))
  simp only [eval_mul,eval_sub,eval_c,eval_pub,hl] at cc
  grind

/-- The single token run ends at the exact native public token total. -/
theorem ListChain.final_token_value {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e)
    (hb : ∀ j,j<16 → pubNat pub (PH_BURNT+j)<256) :
    tokenAt tr tt (e-1)=leN' (pubBytes pub PH_BURNT 16) := by
  rw [show pubBytes pub PH_BURNT 16=(List.range 16).map (fun j => pubNat pub (PH_BURNT+j)) from rfl,leN'_rows _ hb]
  apply sumL_congr
  intro j hj
  simp [cv,pubNat,ListChain.final_token_bytes hL h j hj]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
