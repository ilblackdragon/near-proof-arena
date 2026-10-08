import ZkFormal.NearV3.Candidates.ValueDuplicateMetadata
namespace ZkFormal.NearV3.Candidates.CombinedStoreOccurrences
open ZkFormal.Near ZkFormal.Algebra NearSpec ZkFormal.NearV3.Render StoreDuplicateMetadata

def nodeOccurrences (vs : List NodeS3) : List Occurrence :=
  vs.zipIdx.map fun p=>⟨nodeKey p.1,eidN p.2⟩
def valueOccurrences (tau : ValE→Nat) (es : List ValE) : List Occurrence :=
  es.map fun e=>⟨(tau e,toBytes e.bytes),eidV e⟩
def allOccurrences (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) : List Occurrence :=
  nodeOccurrences vs++valueOccurrences tau es

theorem node_covered (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (i : Nat) (hi : i<vs.length) :
    ∃r∈allOccurrences vs tau es,r.key=nodeKey vs[i] := by
  refine ⟨⟨nodeKey vs[i],eidN i⟩,List.mem_append_left _ (List.mem_map.mpr ⟨(vs[i],i),?_,rfl⟩),rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)

theorem value_covered (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (e : ValE) (he : e∈es) :
    ∃r∈allOccurrences vs tau es,r.key=(tau e,toBytes e.bytes) := by
  exact ⟨⟨(tau e,toBytes e.bytes),eidV e⟩,List.mem_append_right _ (List.mem_map.mpr ⟨e,he,rfl⟩),rfl⟩

/-- Node and value records use the same actual class representative. Coverage
makes the lookup fallback unreachable for every constructed native occurrence. -/
theorem node_representative (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (i : Nat) (hi : i<vs.length) :
    ∃r∈allOccurrences vs tau es,r.key=nodeKey vs[i] ∧
      (patch (allOccurrences vs tau es) i vs[i]).repE=r.eid :=
  representative_found _ _ (node_covered vs tau es i hi)

theorem value_representative (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (e : ValE) (he : e∈es) :
    ∃r∈allOccurrences vs tau es,r.key=(tau e,toBytes e.bytes) ∧
      (ValueDuplicateMetadata.patch (allOccurrences vs tau es) (tau e) e).repE=r.eid :=
  representative_found _ _ (value_covered vs tau es e he)

theorem assigned_wf (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : NodeWf3 vs) (hv : ValWf es)
    (hid : ∀r∈allOccurrences vs tau es,r.eid<P) :
    NodeWf3 (assign (allOccurrences vs tau es) 0 vs) ∧
    ValWf (ValueDuplicateMetadata.assign (allOccurrences vs tau es) tau es) :=
  ⟨assign_wf _ _ hn hid,ValueDuplicateMetadata.assign_wf _ _ _ hv hid⟩
end ZkFormal.NearV3.Candidates.CombinedStoreOccurrences
