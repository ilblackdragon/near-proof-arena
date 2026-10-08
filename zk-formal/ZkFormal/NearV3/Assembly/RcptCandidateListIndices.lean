import ZkFormal.NearV3.Assembly.RcptCandidateListConstants
-- Source ListIndices.lean SHA256: 67d13b080449bdf8e91ea7723acdca7abe96bba12caaa9d4920fc7f92c83c9d3.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ListConstants

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
theorem ListChain.first_wf {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    ∃ B, B.start=s ∧ ListBlockWf tr tt B := by
  cases h with
  | last hw _ => exact ⟨_,rfl,hw⟩
  | cons hw _ => exact ⟨_,rfl,hw⟩

include hL

/-- The list-index field is the header index plus the position in the extracted chain. -/
theorem ListChain.indices {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    ∀ k (hk : k<bs.length), tr.cell tt bs[k].start j=tr.cell tt s j+(k : Fp) := by
  induction h with
  | last hw _ =>
    intro k hk
    have hz : k=0 := by simp only [List.length_singleton] at hk; omega
    subst k
    simp only [List.getElem_cons_zero]
    grind
  | @cons B tail stop hw ht ih =>
    intro k hk
    cases k with
    | zero => simp only [List.getElem_cons_zero]; grind
    | succ k =>
      have hn : tr.cell tt B.stop j=tr.cell tt B.start j+1 := by
        obtain ⟨C,hs,hc⟩ := ht.first_wf
        simpa only [hs] using ListBlockWf.next_index hL hw hc hs
      have hh := ih k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      rw [hh,hn,natCast_add]
      grind

/-- Physical row-zero indices are the natural source-list positions cast into the field. -/
theorem ListChain.zero_indices {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    ∀ k (hk : k<bs.length), tr.cell tt bs[k].start j=(k : Fp) := by
  intro k hk
  have hh := ListChain.indices hL h k hk
  have hp := height_ge hL
  rw [(first0 hL (by omega)).1] at hh
  grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
