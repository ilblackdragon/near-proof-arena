import ZkFormal.NearV3.Rcpt.Candidates.NativeSlotSelection
import ZkFormal.NearV3.Rcpt.Candidates.NativeFillers
import ZkFormal.NearV3.Rcpt.Candidates.PreparedShuffle
import ZkFormal.NearV3.Rcpt.Candidates.PreparedKeyCount

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly

/-- The dictionary portion of native source semantics. Applied receipts and
routing are separate semantic fields, as are global encoded-witness bounds. -/
structure SourceDictionaryFacts (k : WalkD0) (dictionary : List DictionaryEntryV3) : Prop where
  selected : ∀ B∈k.sourceBlks,∀ x∈B.slots,x.1.heightIncluded == B.hdr.height →
    ∃ e : SourceEntryV3,Sum.inl e∈dictionary ∧
      lookupLast (chunkHash x.1.inner x.2.encodedMerkleRoot) (dictionary.map DictionaryEntryV3.entry)=some e.entry ∧
      e.fromShard=x.2.shardId ∧ e.toShard=k.H.shardId ∧ verifyReceiptProof x.2.prevOutgoingReceiptsRoot e.entry=true
  shuffle : ∀ B∈k.sourceBlks,∃ shuffled,
    shuffleWithSeed (selectedProofs (dictionary.map DictionaryEntryV3.entry) B B.slots) B.hdr.prevHash=some shuffled
  dictionaryCount : (distinctKeys (dictionary.map DictionaryEntryV3.entry)).length=(sourceKeysV3 k).length

end ZkFormal.NearV3.Rcpt.Candidates

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec
open NearSpecV3 (Prep Hint WalkD0 ChunkSlot ChunkInner chunkHash)

/-- Source AIR, authenticated receipt/SHA traffic and actual public preparation
produce an executable native dictionary with all three structural source fields.
Fresh filler entries and native shuffle success are derived, not premises. -/
theorem BlockChain.native_dictionary_facts
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
    : SourceDictionaryFacts k
      (nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs (nativeFillers p.lists)) := by
  have hp := (prepSourceD0_sound hprep).1
  have hn := prepD0_source_count hp
  have hsel : ∀ B∈k.sourceBlks,∀ x∈B.slots,x.1.heightIncluded == B.hdr.height →
      ∃ e : Assembly.SourceEntryV3,
        Sum.inl e∈nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs (nativeFillers p.lists) ∧
        NearSpecV3.lookupLast (chunkHash x.1.inner x.2.encodedMerkleRoot)
          ((nativeDictionary p.lists p.hdr.own (ls.map (RcptV3Proof.ListBlock.view rcpt tr)) bs (nativeFillers p.lists)).map
            Assembly.DictionaryEntryV3.entry)=some e.entry ∧
        e.fromShard=x.2.shardId ∧ e.toShard=k.H.shardId ∧
        NearSpecV3.verifyReceiptProof x.2.prevOutgoingReceiptsRoot e.entry=true := by
    intro B hB x hx hnew
    exact hs.native_slot_selected hsrc hrcpt hr hpub hbalance hsha rcOthers srcOthers
      hrbytes hrother hsbytes hsother hdigest hprep hsourcepub hown
      (nativeFillers p.lists) (nativeFillers_fresh p.lists) hw hB hx hnew
  refine ⟨hsel,?_,?_⟩
  · apply prepD0_selected_shuffle hp hw _ k.H.shardId
    intro B hB x hx hnew
    obtain ⟨e,_,hl,hf,ht,hv⟩ := hsel B hB x hx hnew
    exact ⟨e.entry,hl,hf,ht,hv⟩
  · rw [nativeFillers_dictionary_count p.lists hn,prepD0_source_keys_count hp hw]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
