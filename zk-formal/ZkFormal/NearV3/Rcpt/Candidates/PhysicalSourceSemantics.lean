import ZkFormal.NearV3.Rcpt.Candidates.PhysicalOrderedReceipts
import ZkFormal.NearV3.Rcpt.Candidates.NativeAppliedBinding

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec
open NearSpecV3 (Prep Hint WalkD0 ChunkSlot ChunkInner chunkHash)

theorem BlockChain.native_source_semantics
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions src ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (rcOthers srcOthers : List Msg)
    (hrbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) B_BYTES++rcOthers) m)
    (hrother : ∀ m∈rcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    (hsbytes : ∀ m,shaR B_BYTES m=cnt (sourceMsgs src ts bs B_BYTES true++srcOthers) m)
    (hsother : ∀ m∈srcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs src ts bs B_DIGEST false,0<shaS B_DIGEST m.toFp)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hprep : prepSourceD0 cb hint=.ok p)
    (hsourcepub : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    {k : WalkD0} (hw : NearSpecV3.walkD0 cb=.ok k)
    {x : Assembly.ExtV3}
    (hx : x.receipts=ls.map (RcptV3Proof.ListBlock.view rcpt tr))
    (hd : x.dictionary=nativeDictionary p.lists p.hdr.own x.receipts bs (nativeFillers p.lists))
    (hroute : ∀ r∈flatR x.receipts,k.L.shardOf r.toRcptV.toReceipt.receiverId=k.H.shardId) :
    Assembly.SourceSemanticsV3 k x := by
  have hp := (prepSourceD0_sound hprep).1
  have hfacts := hs.native_dictionary_facts hsrc hrcpt hr hpub hbalance hsha rcOthers srcOthers
    hrbytes hrother hsbytes hsother hdigest hprep hsourcepub hown hw
  have hfacts : SourceDictionaryFacts k x.dictionary := by
    simpa only [hd,hx] using hfacts
  have hn : p.lists.length<P := by
    have hh := prepD0_source_count hp
    unfold P
    omega
  have hordered := hs.native_ordered_receipts hsrc hrcpt hr hpub hbalance
    p.lists hn hsourcepub p.hdr.own (nativeFillers p.lists) (nativeFillers_fresh p.lists)
    k.L k.H.shardId (by simpa only [←hx] using hroute)
  apply nativeDictionary_prepared_sourceSemantics hp hw bs (nativeFillers p.lists) hd hfacts hroute
  simpa only [hd,hx,Assembly.ExtV3.applied] using hordered

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
