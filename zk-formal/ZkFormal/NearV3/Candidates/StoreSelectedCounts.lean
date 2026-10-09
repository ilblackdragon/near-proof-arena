import ZkFormal.NearV3.Candidates.StoreSelectedClasses
namespace ZkFormal.NearV3.Candidates.StoreSelectedCounts
open ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Render
open StoreDuplicateMetadata CombinedStoreOccurrences StoreSelectedClasses HonestStoreRepresentatives

theorem assign_map (rs : List Occurrence) (n : Nat) (vs : List NodeS3) :
    assign rs n vs=(vs.zipIdx n).map (fun p=>patch rs p.2 p.1) := by
  induction vs generalizing n with
  | nil => rfl
  | cons s ss ih => simp [assign,List.zipIdx_cons,ih]

private theorem node_filter_count (rs : List Occurrence) (vs : List NodeS3) :
    ((assign rs 0 vs).filter (fun s=>!s.dup)).length=
      ((nodeOccurrences vs).filter (fun r=>r.eid==representativeId rs r.key)).length := by
  rw [assign_map]
  simp [nodeOccurrences,List.filter_map,List.length_map,patch,Function.comp_def]

private theorem value_filter_count (rs : List Occurrence) (tau : ValE→Nat) (es : List ValE) :
    ((ValueDuplicateMetadata.assign rs tau es).filter (fun e=>!e.dup)).length=
      ((valueOccurrences tau es).filter (fun r=>r.eid==representativeId rs r.key)).length := by
  simp [ValueDuplicateMetadata.assign,valueOccurrences,List.filter_map,List.length_map,
    ValueDuplicateMetadata.patch,Function.comp_def]

/-- Exactly the two counts sent by honest count-extended node/value SIZE tables
sum to the number of selected transition-tagged native byte classes. -/
theorem physical_record_count (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hv : ValWf es) :
    ((assign (allOccurrences vs tau es) 0 vs).filter (fun s=>!s.dup)).length+
      ((ValueDuplicateMetadata.assign (allOccurrences vs tau es) tau es).filter (fun e=>!e.dup)).length=
    (representatives ((allOccurrences vs tau es).map Occurrence.key)).length := by
  rw [node_filter_count,value_filter_count,←selected_count _ (combined_ids vs tau es hv)]
  simp only [selected,allOccurrences,List.filter_append,List.length_append]
end ZkFormal.NearV3.Candidates.StoreSelectedCounts
