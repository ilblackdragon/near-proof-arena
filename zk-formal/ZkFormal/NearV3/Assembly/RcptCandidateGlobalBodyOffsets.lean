import ZkFormal.NearV3.Assembly.RcptCandidateListBodyOffsets
-- Source GlobalBodyOffsets.lean SHA256: b6e1a478328791e4ee657b3a8e8c0fa15c177cd682a3b4dda4d6672d58000ae8.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ListBodyOffsets

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Header body offsets follow the exact prefix sum of all enabled refund bytes. -/
theorem ListChain.body_offsets {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    ∀ k (hk : k<bs.length), tr.cell tt bs[k].start o2=
      tr.cell tt s o2+((((bs.take k).map fun B => B.refundBytes tr tt).sum : Nat) : Fp) := by
  induction h with
  | last hw _ =>
    intro k hk
    have hz : k=0 := by simp only [List.length_singleton] at hk; omega
    subst k
    simp only [List.getElem_cons_zero,List.take_zero,List.map_nil,List.sum_nil]
    grind
  | @cons B tail stop hw ht ih =>
    intro k hk
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero,List.take_zero,List.map_nil,List.sum_nil]
      grind
    | succ k =>
      obtain ⟨C,hs,hc⟩ := ht.first_wf
      have hn := ListBlockWf.next_body_offset hL hw hc hs
      rw [hs] at hn
      have hh := ih k (by simpa using hk)
      simp only [List.getElem_cons_succ,List.take_succ_cons,List.map_cons,List.sum_cons,natCast_add]
      rw [hh,hn]
      grind


/-- Body bytes begin at eight, after the native public body prefix. -/
theorem ListChain.zero_body_offsets {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    ∀ k (hk : k<bs.length), tr.cell tt bs[k].start o2=
      (((8+((bs.take k).map fun B => B.refundBytes tr tt).sum) : Nat) : Fp) := by
  intro k hk
  have hh := ListChain.body_offsets hL h k hk
  have hp := height_ge hL
  rw [(first0 hL (by omega)).2.2] at hh
  rw [hh,natCast_add]
  rfl

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
