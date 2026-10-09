import ZkFormal.NearV3.Rcpt.Candidates.NativeSourceSize
import ZkFormal.NearV3.Rcpt.Candidates.NativeEntryShape
import ZkFormal.NearV3.Rcpt.Candidates.NativeSizePartition

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec
open NearSpecV3 (Prep Hint WalkD0)

/-- Exact native dictionary vector length from actual source/receipt AIR and SHA
traffic. The source SIZE charge already includes skipped twelve-byte headers;
only 44 bytes per public occurrence plus the vector prefix remain as overhead. -/
theorem BlockChain.native_dictionary_size
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
    (hprep : NearSpecV3.prepD0 cb hint=.ok p)
    (hsourcepub : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    {k : WalkD0} (hw : NearSpecV3.walkD0 cb=.ok k) :
    (NearSpecV3.encList V3.encodeEntry
      ((nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs
        (nativeFillers p.lists)).map Assembly.DictionaryEntryV3.entry)).length=
      DedupRender.size bs+44*p.lists.length+4 := by
  have hmeta := hs.indexed_metadata hsrc hprep hsourcepub
  have hshape := hs.first_entry_shape hsrc hprep hw hsourcepub (ls.map (RcptV3Proof.ListBlock.view rcpt tr))
  rw [nativeDictionary_encoded_size p.lists (prepD0_source_count hprep) p.hdr.own _ bs
    (fun e he => (hshape e he).1) (fun e he => (hshape e he).2)]
  have he := source_size_partition p.lists bs p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr))
    hmeta.1 (fun i hi => (hmeta.2 i hi).2)
    (by
      intro i hi hd
      have hh := (hs.payload_wf hsrc).blocks (bs.getD i default) (by
        rw [getD_eq_getElem' bs default hi]
        exact List.getElem_mem hi)
      simp only [hd,ite_true] at hh
      exact hh.1)
    (by
      intro i hi hd
      exact hs.native_entry_charge hsrc hrcpt hr hpub hbalance hsha rcOthers srcOthers
        hrbytes hrother hsbytes hsother hdigest hprep hsourcepub hown i hi hd)
  rw [he]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
