import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionaryRouting
import ZkFormal.NearV3.Assembly.PreparedSources

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near NearSpec NearSpecV3 Assembly

/-- Actual preparation fixes the precise shuffled order of the native applied
receipts. Only the occurrence-wise dictionary/list correspondence remains. -/
theorem SourceDictionaryFacts.prepared_applied {cb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {x : ExtV3} (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k)
    (h : SourceDictionaryFacts k x.dictionary)
    (hocc : p.lists.flatMap (sourceReceipts (x.dictionary.map DictionaryEntryV3.entry)
      k.H.shardId k.L)=x.applied) : appliedReceipts k (stateWitnessOfV3 k x)=x.applied := by
  have hv : ∀ B∈k.sourceBlks,∀ slot∈B.slots,
      SourceSlotValid (stateWitnessOfV3 k x).entries k.H.shardId B slot := by
    intro B hB slot hslot hnew
    obtain ⟨e,_,hl,hf,ht,hv⟩ := h.selected B hB slot hslot hnew
    exact ⟨e.entry,hl,hf,ht,hv⟩
  have he := preparedSourceLists_applied hv (prepD0_source_lists hp hw)
  exact he.symm.trans hocc

/-- Concrete native source semantics from actual prepared occurrence binding,
with shuffle/count facts and routing already tied to the same receipt view. -/
theorem nativeDictionary_prepared_sourceSemantics {cb : Bytes} {hint : Hint} {p : Prep}
    {k : WalkD0} {x : ExtV3} (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k)
    (bs : List SrcpB) (fillers : List ProofEntry)
    (hd : x.dictionary=nativeDictionary p.lists p.hdr.own x.receipts bs fillers)
    (h : SourceDictionaryFacts k x.dictionary)
    (hr : ∀ r∈flatR x.receipts,k.L.shardOf r.toRcptV.toReceipt.receiverId=k.H.shardId)
    (hocc : p.lists.flatMap (sourceReceipts (x.dictionary.map DictionaryEntryV3.entry)
      k.H.shardId k.L)=x.applied) : SourceSemanticsV3 k x := by
  exact nativeDictionary_sourceSemantics p.lists p.hdr.own bs fillers hd h hr
    (h.prepared_applied hp hw hocc)

end ZkFormal.NearV3.Rcpt.Candidates
