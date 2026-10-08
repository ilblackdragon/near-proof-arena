import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedScheduler

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec Assembly

private theorem slot_ref_length {a b : Slot} (h : WriteSlotPair a b) :
    a.valueRef.length=b.valueRef.length := by
  cases h <;> simp [Slot.valueRef,NearSpec.u32,NearSpec.leN_length]

theorem write_hash_length {a b : PTrie} (h : WriteTreePair a b) : a.hashOf.length=b.hashOf.length := by
  cases h with
  | hash=>rfl
  | leaf=>simp [PTrie.hashOf]
  | ext=>simp [PTrie.hashOf]
  | branch m hv hs=>cases hv <;> simp [PTrie.hashOf]

theorem write_kids_hash_length : ∀{a b : Kids},WriteKidsPair a b→a.hashes.length=b.hashes.length
  | _,_,.nil=>rfl
  | _,_,.none h=>by simpa only [Kids.hashes] using write_kids_hash_length h
  | _,_,.some h hs=>by simp only [Kids.hashes,List.length_append,write_hash_length h,write_kids_hash_length hs]

/-- Old-node encodings keep their exact lengths even when value lengths change:
value references themselves have fixed encoded width. -/
theorem write_node_length {a b : PTrie} (h : WriteTreePair a b) :
    (nodeEnc a).length=(nodeEnc b).length := by
  cases h with
  | hash=>rfl
  | leaf k m hs=>simp only [nodeEnc,List.length_append,slot_ref_length hs]
  | ext k m hc=>simp only [nodeEnc,List.length_append,write_hash_length hc]
  | branch m hv hs=>
    cases hv with
    | none=>simp [nodeEnc,write_kids_hash_length hs,native_pair_bitmap hs]
    | some h=>simp [nodeEnc,write_kids_hash_length hs,native_pair_bitmap hs,slot_ref_length h]

theorem OccurrencePairs.node_lengths {as bs : List PTrie} (h : OccurrencePairs as bs) :
    as.map (fun t=>(nodeEnc t).length)=bs.map (fun t=>(nodeEnc t).length) := by
  induction h with
  | nil=>rfl
  | cons hp ht ih=>simp only [List.map_cons,write_node_length hp,ih]

/-- The complete unfolded native byte charge survives actual sized receipt
replay, so scheduler allocation retains its original accepted byte budget. -/
theorem SizedAccountRun.unfolded_bytes {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : SizedAccountRun pre writes post) :
    NearSpecV3.unfoldedBytesT post=NearSpecV3.unfoldedBytesT pre := by
  have hn:=(paired_occurrences h.forget.skeleton).node_lengths
  have hv:=h.value_lengths
  simp only [NearSpecV3.unfoldedBytesT,Assembly.native_occs_eq,Assembly.native_valsOf_eq]
  have he : ∀t : PTrie,NearSpecV3.nodeEnc t=nodeEnc t := by
    intro t
    cases t with
    | hash h=>rfl
    | leaf k s m=>rfl
    | ext k c m=>rfl
    | branch v cs m=>cases v <;> rfl
  simp only [he]
  rw [←hn,hv]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
