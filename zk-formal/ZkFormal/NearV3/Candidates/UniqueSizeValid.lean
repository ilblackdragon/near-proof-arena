import ZkFormal.NearV3.Candidates.SizeChargeFields
import ZkFormal.NearV3.Candidates.UniqueSizeComponents
namespace ZkFormal.NearV3.Candidates.UniqueSizeValid
open ZkFormal.Near Render UniqueSizeComponents
/-- Remaining total-budget input is native encoded accounting, not an AIR
slack/constraint assumption: original stores plus source bytes and public overhead. -/
theorem native_valid (ts : List NearSpec.PTrie) (store : Nat→List NearSpec.Bytes)
    (hw : ∀t∈ts,t.wf=true) (hb : Assembly.preBytes ts≤2000000)
    (hn : NodeWf3 (Assembly.forestNodes 0 0 0 ts))
    (hs : ∀p∈ts.zipIdx,Stored (NearSpecV3.mkStore (store p.2)) p.1)
    (pub : List ZkFormal.Algebra.Fp) (bs : List SrcpB)
    (htotal : ovhNat pub+UniqueSourceCharge.size bs+
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store)≤8388608) :
    let vs:=Assembly.forestNodes 0 0 0 ts
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    SizeCountReceiver.Valid pub (view ns vals bs) (counts ns vals) := by
  dsimp only
  refine ⟨SizeChargeFields.native_base ts hw hb hn bs,?_⟩
  let vs:=Assembly.forestNodes 0 0 0 ts
  let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
  let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
  have hv:=ChainMetadata.value_wf cs es (NativeValueWf.forest_wf ts hw hb)
    (StoreClassPartition.combined_metadata vs _ es hn (NativeValueWf.forest_wf ts hw hb)).2.1
  have hf:=SizeChargeFields.fields_charge (ChainMetadata.assign cs 0 vs) (ChainMetadata.assignValues cs es) bs hv
  have hc:=ChainStoreCharge.native_charge ts store hw hb hs
  change _+_+_+UniqueSourceCharge.size bs+_≤8388608
  dsimp only [vs,es,cs] at hf
  dsimp only at hc
  simp only [SizeComponents.view,SizeComponents.counts,UniqueSizeComponents.view,UniqueSizeComponents.counts] at hf ⊢
  omega

end ZkFormal.NearV3.Candidates.UniqueSizeValid
