import ZkFormal.NearV3.Assembly.RcptCandidateRclProof
-- Source RclDecode.lean SHA256: dbc10b4ac3dcb77c269cb4fc10c3ce6a898f49c4b58d552157d5f6beedf8cc54.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.RclProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Every list consumes at least its twelve header rows, so list indices cannot wrap. -/
theorem ListChain.length_le_rows {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    12*bs.length≤e-s := by
  induction h with
  | last hw _ =>
    have hs := hw.stop_eq
    simp only [List.length_singleton]
    unfold ListBlock.rows at hs
    omega
  | @cons B tail stop hw ht ih =>
    have hs := hw.stop_eq
    have hb := ht.rows
    simp only [List.length_cons]
    unfold ListBlock.rows at hs
    omega

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem ListChain.length_lt_P {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    bs.length<P := by
  have := h.length_le_rows
  have := h.end_padding.1
  have := hP hL
  omega

/-- Field-valued RCL records decode to the unique natural list index and its actual length. -/
theorem ListChain.rcl_decode {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    {k len : Nat} (hk : k<P) (hlen : len<P)
    (hm : [(k : Fp),(len : Fp)]∈bs.map (listRclRecord tr tt)) :
    ∃ hk' : k<bs.length,
      lOffs (bs[k].viewReceipts tr tt) (bs[k].viewReceipts tr tt).length=len := by
  obtain ⟨B,hB,hrec⟩ := List.mem_map.mp hm
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hB
  have hind := ListChain.zero_indices hL h i hi
  rw [he] at hind
  have hw := h.blocks B hB
  simp only [listRclRecord,List.cons.injEq] at hrec
  have hidx : i=k := ofNat_inj (by have := ListChain.length_lt_P hL h; omega) hk (hind.symm.trans hrec.1)
  subst i
  refine ⟨hi,?_⟩
  rw [he]
  exact ofNat_inj (ListBlockWf.encoded_lt_P hL hw) hlen hrec.2.1

/-- A matched source length twelve forces the actual applied receipt list to be empty. -/
theorem ListChain.rcl_twelve_empty {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    {k : Nat} (hk : k<P)
    (hm : [(k : Fp),((12 : Nat) : Fp)]∈bs.map (listRclRecord tr tt)) :
    ∃ hk' : k<bs.length, bs[k].receipts=[] := by
  obtain ⟨hi,hlen⟩ := ListChain.rcl_decode hL h hk (by decide) hm
  exact ⟨hi,(bs[k].encoded_eq_twelve tr tt).mp hlen⟩

/-- The same empty-list conclusion uses actual physical receipt-table RCL traffic. -/
theorem ListChain.physical_rcl_twelve_empty {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    {k : Nat} (hk : k<P)
    (hm : [(k : Fp),((12 : Nat) : Fp)]∈
      (List.range (tr.height tt)).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_RCL true)) :
    ∃ hk' : k<bs.length, bs[k].receipts=[] := by
  rw [ListChain.rcl_full hL h] at hm
  exact ListChain.rcl_twelve_empty hL h hk hm

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
