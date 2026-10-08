import ZkFormal.NearV3.Candidates.UniqueSourceDictionarySize
import ZkFormal.NearV3.Candidates.UniqueSourceSoundShadow
import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionarySizeBinding
namespace ZkFormal.NearV3.Candidates.UniqueSourceDictionarySound
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec
open Rcpt.Candidates Rcpt.Candidates.DedupProof UniqueSourceSoundShadow
open NearSpecV3 (Prep Hint WalkD0)
theorem encoded_dictionary
    {src rcpt : Trace Fp} {ts tr : Nat} {pub : List Fp}
    (hsrc : TableLocal (UniqueSourceCharge.table 24) src ts pub)
    (hrcpt : TableLocal RcptV3.table rcpt tr pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain (shadow src) ts 0 bs se)
    {ls : List RcptV3Proof.ListBlock} {re : Nat} (hr : RcptV3Proof.ListChain rcpt tr 0 ls re)
    (hpub : RcptV3Proof.ReceiptPublicRanges pub)
    (hbalance : ∀ m : List Fp,
      ((List.range (src.height ts)).flatMap (fun q => rowTraffic DedupTable.interactions (shadow src) ts q pub B_RCL false)).count m=
      ((List.range (rcpt.height tr)).flatMap (fun q => rowTraffic RcptV3.interactions rcpt tr q pub B_RCL true)).count m)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (rcOthers srcOthers : List Msg)
    (hrbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) B_BYTES++rcOthers) m)
    (hrother : ∀ m∈rcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    (hsbytes : ∀ m,shaR B_BYTES m=cnt (sourceMsgs (shadow src) ts bs B_BYTES true++srcOthers) m)
    (hsother : ∀ m∈srcOthers,∀ a,m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs (shadow src) ts bs B_DIGEST false,0<shaS B_DIGEST m.toFp)
    {cb : Bytes} {hint : Hint} {p : Prep}
    (hprep : NearSpecV3.prepD0 cb hint=.ok p)
    (hsourcepub : ∀ m,cnt (sourceMsgs (shadow src) ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 p.hdr.own)
    {k : WalkD0} (hw : NearSpecV3.walkD0 cb=.ok k) :
    (NearSpecV3.encList V3.encodeEntry
      ((nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs
        []).map Assembly.DictionaryEntryV3.entry)).length=
      UniqueSourceCharge.size bs+4 := by
  have hsrc0:=old_local hsrc
  have hmeta := hs.indexed_metadata hsrc0 hprep hsourcepub
  have hshape := hs.first_entry_shape hsrc0 hprep hw hsourcepub (ls.map (RcptV3Proof.ListBlock.view rcpt tr))
  apply UniqueSourceDictionarySize.encoded_size p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs
    hmeta.1 (fun i hi => (hmeta.2 i hi).2)
    (by
      intro i hi hd
      have hh := (hs.payload_wf hsrc0).blocks (bs.getD i default) (by
        rw [getD_eq_getElem' bs default hi]
        exact List.getElem_mem hi)
      simp only [hd,ite_true] at hh
      exact hh.1)
    (by
      intro i hi hd
      exact hs.native_entry_charge hsrc0 hrcpt hr hpub hbalance hsha rcOthers srcOthers
        hrbytes hrother hsbytes hsother hdigest hprep hsourcepub hown i hi hd)
  · exact fun e he=>(hshape e he).1
  · exact fun e he=>(hshape e he).2

end ZkFormal.NearV3.Candidates.UniqueSourceDictionarySound
