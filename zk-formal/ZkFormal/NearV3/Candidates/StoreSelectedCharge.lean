import ZkFormal.NearV3.Candidates.StoreSelectedCounts
namespace ZkFormal.NearV3.Candidates.StoreSelectedCharge
open ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Render
open StoreDuplicateMetadata CombinedStoreOccurrences StoreSelectedClasses StoreSelectedCounts HonestStoreRepresentatives

def nodeCharge (vs : List NodeS3) : Nat :=
  ((vs.filter fun s=>!s.dup).map fun s=>(s.v.ser false).length+4).sum
def valueCharge (es : List ValE) : Nat :=
  ((es.filter fun e=>!e.dup).map fun e=>e.bytes.length+4).sum

private theorem node_charge (rs : List Occurrence) (vs : List NodeS3) :
    nodeCharge (assign rs 0 vs)=
      (((nodeOccurrences vs).filter fun r=>r.eid==representativeId rs r.key).map
        fun r=>r.key.2.length+4).sum := by
  simp [nodeCharge,assign_map,nodeOccurrences,List.filter_map,List.map_map,patch,nodeKey,toBytes,Function.comp_def]

private theorem value_charge (rs : List Occurrence) (tau : ValE→Nat) (es : List ValE) :
    valueCharge (ValueDuplicateMetadata.assign rs tau es)=
      (((valueOccurrences tau es).filter fun r=>r.eid==representativeId rs r.key).map
        fun r=>r.key.2.length+4).sum := by
  simp [valueCharge,ValueDuplicateMetadata.assign,valueOccurrences,List.filter_map,List.map_map,
    ValueDuplicateMetadata.patch,toBytes,Function.comp_def]

/-- Full payload plus all four-byte length prefixes charged by the actual
selected node/value records equals the native class charge. -/
theorem exact_charge (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) (hv : ValWf es) :
    nodeCharge (assign (allOccurrences vs tau es) 0 vs)+
      valueCharge (ValueDuplicateMetadata.assign (allOccurrences vs tau es) tau es)=
    charge (representatives ((allOccurrences vs tau es).map Occurrence.key)) := by
  rw [node_charge,value_charge,←selected_charge _ (combined_ids vs tau es hv)]
  simp only [charge,selected,allOccurrences,List.filter_append,List.map_append,List.sum_append,List.map_map,Function.comp_def]

/-- Honest SIZE upper-charge obligation reduced to native byte provenance,
not to an assumed numerical accounting bound. -/
theorem native_charge_le (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) (hv : ValWf es)
    (original : List Key) (hc : (allOccurrences vs tau es).map Occurrence.key⊆original) :
    nodeCharge (assign (allOccurrences vs tau es) 0 vs)+
      valueCharge (ValueDuplicateMetadata.assign (allOccurrences vs tau es) tau es)≤charge original := by
  rw [exact_charge vs tau es hv]
  exact charge_le _ _ hc
end ZkFormal.NearV3.Candidates.StoreSelectedCharge
