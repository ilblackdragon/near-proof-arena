import ZkFormal.NearV3.Rcpt.Candidates.NativeOccurrence

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

theorem BlockChain.repeated_occurrence_empty
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
    {i : Nat} (hi : i<sources.length) (hrep : sourceRepeated sources i=true) :
    ((ls.map (RcptV3Proof.ListBlock.view rcpt tr)).getD i default).rs=[] := by
  have hmeta := hs.bind_public hsrc sources hn hpublic
  have hib : i<bs.length := by omega
  let B := bs[i]
  have hB : B∈bs := List.getElem_mem hib
  have hj : B.j=i := by
    have hh := hs.j_indices hsrc i hib
    rw [(row0 hsrc).2.1] at hh
    simpa only [show Fp.toNat 0=0 from rfl,Nat.zero_add] using hh
  obtain ⟨rep,hview⟩ := sourceViews_mem (tr := src) (tt := ts) (s := 0) hB
  have hL := (hmeta.2 (B,rep) hview).2.2.2.2
  have hLen : B.L=12 := hL (by simpa only [hj] using hrep)
  obtain ⟨hil,hempty⟩ := hs.receipt_empty_of_twelve hsrc hrcpt hr hbalance hB hLen
  simp only [hj] at hil hempty
  rw [getD_eq_getElem' _ default (by simpa only [List.length_map] using hil)]
  simp only [List.getElem_map,RcptV3Proof.ListBlock.view,RcptV3Proof.ListBlock.viewReceipts,hempty,List.map_nil]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
