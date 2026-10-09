import ZkFormal.NearV3.Candidates.InitializedStoreAccounting
namespace ZkFormal.NearV3.Candidates.InitializedSizeValid
open ZkFormal.Near Rcpt.Candidates.NodePostUpdate SizeComponents

/-- Concrete initialized native metadata replaces the raw NodeWf assumption.
The initializer preserves duplicate classes and encoded store charge. -/
theorem native_valid (ts : List NearSpec.PTrie) (store : Nat→List NearSpec.Bytes)
    (hw : ∀t∈ts,t.wf=true) (hb : Assembly.preBytes ts≤2000000)
    (hd : ∀t∈ts,∀k,fdepth t k≤NearSpecV3.trieFuel)
    (ht : ts.length≤ZkFormal.Algebra.P)
    (hs : ∀p∈ts.zipIdx,Stored (NearSpecV3.mkStore (store p.2)) p.1)
    (pub : List ZkFormal.Algebra.Fp) (bs : List SrcpB)
    (htotal : ovhNat pub+Rcpt.Candidates.DedupRender.size bs+
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store)≤8388608) :
    let vs:=initializeList 0 (Assembly.forestNodes 0 0 0 ts)
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    SizeCountReceiver.Valid pub (view ns vals bs) (counts ns vals) := by
  let raw:=Assembly.forestNodes 0 0 0 ts
  let vs:=initializeList 0 raw
  let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
  let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
  have hn:=native_forest_wf ts hw hb hd ht
  have he:=NativeValueWf.forest_wf ts hw hb
  have hv:=ChainMetadata.value_wf cs es he
    (StoreClassPartition.combined_metadata vs _ es hn he).2.1
  refine ⟨?_,?_⟩
  · have hp:=SizeChargeFields.chain_payload_le vs (NativeStoreProvenance.valueTau ts) es hn he bs
    have hx:=Rcpt.Candidates.forest_occurrence_bytes ts hw
    simp only [Assembly.forestStoreViews] at hx
    simp only [vs,initializeList_bytes] at hp
    dsimp only [vs,raw,es,cs] at hp
    omega
  · have hf:=SizeChargeFields.fields_charge (ChainMetadata.assign cs 0 vs)
      (ChainMetadata.assignValues cs es) bs hv
    have hc:=ChainStoreCharge.native_charge ts store hw hb hs
    have hh : StoreSelectedCharge.nodeCharge (ChainMetadata.assign cs 0 vs)+
        StoreSelectedCharge.valueCharge (ChainMetadata.assignValues cs es)≤
        HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store) := by
      dsimp only [cs,vs,raw,es]
      rw [InitializedStoreAccounting.occurrences,InitializedStoreAccounting.node_charge]
      exact hc
    change _+_+_+Rcpt.Candidates.DedupRender.size bs+_≤8388608
    dsimp only [vs,raw,es,cs] at hf hh
    omega
end ZkFormal.NearV3.Candidates.InitializedSizeValid
