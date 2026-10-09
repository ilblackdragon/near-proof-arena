import ZkFormal.NearV3.Rcpt.Candidates.PhysicalSourceCount

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

theorem BlockChain.native_ordered_receipts
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    (sources : List NearSpecV3.SrcList) (hn : sources.length<P)
    (hpublic : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records sources) m)
    (own : Nat) (fillers : List NearSpecV3.ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈sources,f.key≠s.key)
    (L : NearSpecV3.Layout) (target : Nat)
    (hroute : ∀ x∈flatR (ls.map (RcptV3Proof.ListBlock.view rcpt tr)),
      L.shardOf x.toRcptV.toReceipt.receiverId=target) :
    sources.flatMap (sourceReceipts
      ((nativeDictionary sources own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs fillers).map
        Assembly.DictionaryEntryV3.entry) target L)=
      (ls.map (RcptV3Proof.ListBlock.view rcpt tr)).flatMap
        (fun l => l.rs.map (fun r => r.toRcptV.toReceipt)) := by
  have hcount := hs.receipt_list_count hsrc hrcpt hr hpub hbalance
  have hmeta := (hs.bind_public hsrc sources hn hpublic).1
  apply nativeDictionary_ordered_receipts sources own _ bs fillers hf
  · intro i hi hrep
    exact hs.repeated_occurrence_empty hsrc hrcpt hr hpub hbalance sources hn hpublic hi hrep
  · simp only [List.length_map]
    omega
  · exact hroute

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
