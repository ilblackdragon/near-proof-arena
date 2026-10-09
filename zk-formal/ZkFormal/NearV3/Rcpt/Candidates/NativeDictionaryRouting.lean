import ZkFormal.NearV3.Assembly.Good
import ZkFormal.NearV3.Rcpt.Candidates.NativeSourceDictionary
import ZkFormal.NearV3.Rcpt.Link.PreparedNativeRouting

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near NearSpec NearSpecV3 Assembly

/-- A representative source entry contains only receipts from the same input
view; missing indices have the empty default list. -/
theorem nativeEntryAt_receipt_mem (sources : List SrcList) (own : Nat)
    (rs : RcptV3Vs) (bs : List SrcpB) (i : Nat) {r : Receipt}
    (hr : r∈(nativeEntryAt sources own rs bs i).entry.receipts) :
    ∃ x∈flatR rs,x.toRcptV.toReceipt=r := by
  change r∈((rs.getD i default).rs.map (fun x => x.toRcptV.toReceipt)) at hr
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
  by_cases hi : i<rs.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] at hx
    exact ⟨x,List.mem_flatMap.mpr ⟨rs[i],List.getElem_mem hi,hx⟩,rfl⟩
  · simp only [List.getD_eq_getElem?_getD,show rs[i]?=none from List.getElem?_eq_none (by omega),Option.getD_none] at hx
    cases hx

/-- Every computational dictionary entry inherits routing from the physical
receipt view. Fillers are a separate branch and cannot enter this theorem. -/
theorem nativeDictionary_inl_routing (sources : List SrcList) (own : Nat)
    (rs : RcptV3Vs) (bs : List SrcpB) (fillers : List ProofEntry)
    (L : Layout) (target : Nat)
    (hr : ∀ x∈flatR rs,L.shardOf x.toRcptV.toReceipt.receiverId=target)
    {e : SourceEntryV3} (he : Sum.inl e∈nativeDictionary sources own rs bs fillers) :
    ∀ r∈e.entry.receipts,L.shardOf r.receiverId=target := by
  rcases List.mem_append.mp he with he|he
  · obtain ⟨e',he',heq⟩ := List.mem_map.mp he
    cases heq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he'
    intro r hrm
    obtain ⟨x,hx,rfl⟩ := nativeEntryAt_receipt_mem sources own rs bs i hrm
    exact hr x hx
  · obtain ⟨_,_,heq⟩ := List.mem_map.mp he
    cases heq

/-- Native used proofs select computational representatives, so dictionary
routing covers repeats without requiring source-key uniqueness. -/
theorem SourceDictionaryFacts.used_routing {k : WalkD0} {dictionary : List DictionaryEntryV3}
    (h : SourceDictionaryFacts k dictionary)
    (hr : ∀ e,Sum.inl e∈dictionary → ∀ r∈e.entry.receipts,
      k.L.shardOf r.receiverId=k.H.shardId)
    (w : StateWitness) (hw : w.entries=dictionary.map DictionaryEntryV3.entry) :
    ∀ e∈usedProofs k w,∀ r∈e.receipts,k.L.shardOf r.receiverId=k.H.shardId := by
  intro e he
  obtain ⟨B,hB,he⟩ := List.mem_flatMap.mp he
  obtain ⟨slot,hslot,he⟩ := List.mem_filterMap.mp he
  rcases slot with ⟨sl,ci⟩
  dsimp only at he
  split at he
  · rename_i hnew
    obtain ⟨s,hs,hlookup,_,_,_⟩ := h.selected B hB (sl,ci) hslot hnew
    rw [hw,hlookup] at he
    cases he
    exact hr s hs
  · cases he

/-- The structural source facts and representative routing leave exactly the
ordered applied-receipt equality to complete native source semantics. -/
theorem SourceDictionaryFacts.sourceSemantics {k : WalkD0} {x : ExtV3}
    (h : SourceDictionaryFacts k x.dictionary)
    (hr : ∀ e,Sum.inl e∈x.dictionary → ∀ r∈e.entry.receipts,
      k.L.shardOf r.receiverId=k.H.shardId)
    (ha : appliedReceipts k (stateWitnessOfV3 k x)=x.applied) : SourceSemanticsV3 k x := by
  refine ⟨?_,?_,h.dictionaryCount,ha,?_⟩
  · intro B hB sl ci hslot hnew
    exact h.selected B hB (sl,ci) hslot hnew
  · intro B hB
    exact h.shuffle B hB
  · exact h.used_routing hr _ rfl

/-- Routing from the SAME complete physical view transfers through the concrete
first-occurrence dictionary, preserving unused fillers and repeated lookups. -/
theorem nativeDictionary_sourceSemantics {k : WalkD0} {x : ExtV3}
    (sources : List SrcList) (own : Nat) (bs : List SrcpB) (fillers : List ProofEntry)
    (hd : x.dictionary=nativeDictionary sources own x.receipts bs fillers)
    (h : SourceDictionaryFacts k x.dictionary)
    (hr : ∀ r∈flatR x.receipts,k.L.shardOf r.toRcptV.toReceipt.receiverId=k.H.shardId)
    (ha : appliedReceipts k (stateWitnessOfV3 k x)=x.applied) : SourceSemanticsV3 k x := by
  apply h.sourceSemantics _ ha
  intro e he
  rw [hd] at he
  exact nativeDictionary_inl_routing sources own x.receipts bs fillers k.L k.H.shardId hr he

end ZkFormal.NearV3.Rcpt.Candidates
