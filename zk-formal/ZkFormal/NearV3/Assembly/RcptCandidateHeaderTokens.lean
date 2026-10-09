import ZkFormal.NearV3.Assembly.RcptCandidateTokenCarry
-- Source HeaderTokens.lean SHA256: a181b0ae7cdd2e46ad8d1731cadc6713bc181c4bd3f37bdbf50e077fd4a180e7.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.TokenCarry

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Tokens are preserved throughout list headers, including empty-list transitions. -/
theorem ListBlockWf.header_tokens {B : ListBlock} (h : ListBlockWf tr tt B)
    (k : Nat) (hk : k≤12) (he : k=12 → tr.cell tt (B.start+12) act=1) :
    ∀ j,j<16 → tr.cell tt (B.start+k) (tok j)=tr.cell tt B.start (tok j) := by
  apply token_span hL B.start k (by have := h.header_fin; omega)
  · intro i hi
    by_cases hi12 : i=12
    · rw [hi12]
      exact he (by omega)
    · have hs := h.header.st i (by omega)
      exact (oneHot hL (by have := h.header_fin; omega) (by simp [states]) hs).1
  · intro i hi
    have hs := h.header.st i (by omega)
    exact (oneHot hL (by have := h.header_fin; omega) (by simp [states]) hs).2 sGP (by simp [states]) (by decide)

/-- The first receipt's incoming GP token state is the list header's token state. -/
theorem ListBlockWf.first_tokens {B : ListBlock} (h : ListBlockWf tr tt B) {y : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (hs : y.s=B.start+12) :
    ∀ j,j<16 → tr.cell tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)=tr.cell tt B.start (tok j) := by
  intro j hj
  rw [token_receipt_start hL hy j hj,hs]
  apply ListBlockWf.header_tokens hL h 12 (by omega) _ j hj
  intro _
  rw [←hs]
  exact (Layout.start_flags hL hy).1

/-- An empty list's terminal token state is its entry state. -/
theorem ListBlockWf.empty_terminal_tokens {B : ListBlock} (h : ListBlockWf tr tt B)
    (he : B.receipts=[]) : ∀ j,j<16 → tr.cell tt (B.stop-1) (tok j)=tr.cell tt B.start (tok j) := by
  have hs : B.stop=B.start+12 := by simp [ListBlock.stop,he,segsOf,segEnd]
  intro j hj
  rw [hs,show B.start+12-1=B.start+11 by omega]
  exact ListBlockWf.header_tokens hL h 11 (by omega) (by omega) j hj

/-- Consecutive receipts share exactly the prior receipt's generated token bytes. -/
theorem token_next_receipt {y z : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hz : Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt) (hs : z.s=y.s+y.tot) :
    ∀ j,j<16 → tr.cell tt (gq z.s z.Lp z.Lv z.Ls z.kt 0) (tok j)=
      ((bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt j) 31 8:Nat):Fp) := by
  intro j hj
  rw [token_receipt_start hL hz j hj]
  have ht : 94+Vt y.Lp y.Lv y.Ls y.kt<y.tot := by unfold RS.tot total; split <;> omega
  have hh := receipt_token_rows hL hy (94+Vt y.Lp y.Lv y.Ls y.kt) y.tot (by omega) (by omega)
    (fun k hk _ => Or.inr hk) (fun _ => by rw [←hs]; exact (Layout.start_flags hL hz).1) j hj
  rw [token_receipt_gp_end hL hy j hj] at hh
  rwa [hs]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
