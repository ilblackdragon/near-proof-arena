import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionaryVerified
import ZkFormal.NearV3.Rcpt.Candidates.PreparedCoverage
import ZkFormal.NearV3.Rcpt.Candidates.PreparedNativeOwner

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec
open NearSpecV3 (Prep Hint WalkD0 ChunkSlot ChunkInner chunkHash)

/-- Actual source/receipt/SHA traffic selects authenticated left-branch entries
for every native included slot, with repeated-key reuse derived from public
metadata. The prepared/native owner identity follows from successful preparation. -/
theorem BlockChain.native_slot_selected
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
    (fillers : List NearSpecV3.ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈p.lists,f.key≠s.key)
    {k : WalkD0} (hw : NearSpecV3.walkD0 cb=.ok k)
    {B : NearSpecV3.Blk} (hB : B∈k.sourceBlks)
    {x : ChunkSlot × ChunkInner} (hx : x∈B.slots)
    (hn : x.1.heightIncluded == B.hdr.height) :
    ∃ e : Assembly.SourceEntryV3,
      Sum.inl e∈nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs fillers ∧
      NearSpecV3.lookupLast (chunkHash x.1.inner x.2.encodedMerkleRoot)
        ((nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs fillers).map
          Assembly.DictionaryEntryV3.entry)=some e.entry ∧
      e.fromShard=x.2.shardId ∧ e.toShard=k.H.shardId ∧
      NearSpecV3.verifyReceiptProof x.2.prevOutgoingReceiptsRoot e.entry=true := by
  have ho := Assembly.prepD0_source_owner (prepSourceD0_sound hprep).1 hw
  have hm := prepD0_source_slot_mem (prepSourceD0_sound hprep).1 hw hB hx hn
  obtain ⟨e,he,hl,hf',ht,hv⟩ := hs.native_dictionary_selected hsrc hrcpt hr hpub hbalance
    hsha rcOthers srcOthers hrbytes hrother hsbytes hsother hdigest hprep hsourcepub hown fillers hf hm
  exact ⟨e,he,hl,hf',ht.trans ho,hv⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
