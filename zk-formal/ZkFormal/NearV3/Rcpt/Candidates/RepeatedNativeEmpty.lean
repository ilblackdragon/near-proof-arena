import ZkFormal.NearV3.Rcpt.Candidates.NativeEmptyList

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

theorem BlockChain.repeated_native_empty
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) B_BYTES++others) m)
    (hother : ∀ m∈others,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    (hdigest : ∀ m∈sourceMsgs src ts bs B_DIGEST false,0<shaS B_DIGEST m.toFp)
    {own : Nat} (hown : toBytes (pubBytes pub PH_OWN 8)=u64 own)
    {B : SrcpB} (hB : B∈bs) (hd : B.dup=false)
    (sources : List NearSpecV3.SrcList) (hn : sources.length<P)
    (hpublic : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records sources) m)
    (hrep : sourceRepeated sources B.j=true) :
    ∃ hi : B.j<ls.length,(ls[B.j].view rcpt tr).rs=[] := by
  obtain ⟨hi,hsize⟩ := hs.native_receipt_size hsrc hrcpt hr hpub hbalance hsha others
    hbytes hother hdigest hown hB hd
  obtain ⟨rep,hview⟩ := sourceViews_mem (tr := src) (tt := ts) (s := 0) hB
  have hmeta := (hs.bind_public hsrc sources hn hpublic).2 (B,rep) hview
  have hL := hmeta.2.2.2.2 hrep
  rw [hL] at hsize
  exact ⟨hi,receipt_view_empty hsize⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
