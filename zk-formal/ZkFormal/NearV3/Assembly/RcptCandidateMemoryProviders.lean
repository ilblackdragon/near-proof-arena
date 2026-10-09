import ZkFormal.NearV3.Assembly.RcptCandidateMemoryVersion
import ZkFormal.NearV3.Rcpt.Extract.AcctProof
import ZkFormal.Near.Link.Bus

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3Proof RcptSkeleton

/-- Receipt writers use their actual global index plus one, bounded by the
physical row capacity independently of semantic receipt Wf. -/
theorem receipt_memory_provider_bound {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal receiptArithmeticCandidate tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e)
    {m : Msg} (hm : m∈rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MEM) :
    m.getD 1 0≤2^22 := by
  rw [←memoryWriteMsgs_view tr tt pub bs] at hm
  simp only [indexedReceiptMsgs,List.mem_flatMap,List.mem_range] at hm
  obtain ⟨j,hj,hm⟩ := hm
  rw [getD_eq_getElem' bs ⟨0,[]⟩ hj] at hm
  obtain ⟨k,hk,hm⟩ := hm
  simp only [memoryWriteMsgs,List.mem_map,List.mem_range] at hm
  obtain ⟨i,hi,rfl⟩ := hm
  simp only [List.getD_cons_succ,List.getD_cons_zero]
  have hn := receipt_prefix_lt bs j hj k hk
  have hr := receipt_counts_le_rows bs
  have hb := hc.rows
  have he := hc.end_padding.1
  have hh := height_le hL
  unfold receiptIndex
  omega

/-- Account providers open version zero, without relying on any account Wf. -/
theorem account_memory_provider_zero {as : List AcctV} {m : Msg}
    (hm : m∈acctV3Sends as B_MEM) : m.getD 1 0=0 := by
  simp only [acctV3Sends,show B_MEM≠B_VBYTES by decide,show B_MEM≠B_BYTES by decide,
    ite_false,ite_true,List.mem_flatMap,List.mem_map,List.mem_range] at hm
  obtain ⟨a,ha,i,hi,rfl⟩ := hm
  rfl

/-- Actual account opens and receipt writes are enough to bound every received
version whenever global ownership establishes count domination by those providers. -/
theorem repaired_previous_of_mem_providers {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e) (as : List AcctV)
    (hproviders : ∀ m : List Fp,
      tableBusCount ReceiptCandidateRouting.candidateTable.interactions tr tt pub B_MEM false m ≤
        cnt (acctV3Sends as B_MEM ++ rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MEM) m) :
    ∀ x∈flatR (bs.map (ListBlock.view tr tt)), x.tprev≤2^22 := by
  apply repaired_previous_of_mem_stream hL hc
  intro m hm
  have hp : 0<cnt (acctV3Sends as B_MEM ++ rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MEM) m :=
    Nat.lt_of_lt_of_le hm (hproviders m)
  obtain ⟨v,hv,rfl⟩ := Link.cnt_pos.mp hp
  have hb : v.getD 1 0≤2^22 := by
    rcases List.mem_append.mp hv with ha|hr
    · rw [account_memory_provider_zero ha]; omega
    · exact receipt_memory_provider_bound (repaired_local_base hL) hc hr
  have he : (v.toFp.getD 1 0).toNat=(v.getD 1 0)%P := by
    cases v with
    | nil => rfl
    | cons a vs =>
      cases vs with
      | nil => rfl
      | cons b tail => exact Fp.toNat_ofNat b
  rw [he,Nat.mod_eq_of_lt (by unfold P; omega)]
  exact hb

/-- Full repaired semantics and traffic, with only public ranges and actual
MEM provider ownership left for the family-level linker. -/
theorem repaired_sound_of_mem_providers {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub) (as : List AcctV)
    (hproviders : ∀ m : List Fp,
      tableBusCount ReceiptCandidateRouting.candidateTable.interactions tr tt pub B_MEM false m ≤
        cnt (acctV3Sends as B_MEM ++ rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MEM) m) :
    RcptV3Wf pub (bs.map (ListBlock.view tr tt)) ∧
      TableTraffic ReceiptCandidateRouting.candidateTable.interactions tr tt pub
        (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) :=
  repaired_view_sound_of_flat hL hc hp (repaired_previous_of_mem_providers hL hc as hproviders)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
