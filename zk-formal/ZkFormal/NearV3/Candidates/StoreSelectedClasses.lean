import ZkFormal.NearV3.Candidates.StoreOccurrenceUnique
namespace ZkFormal.NearV3.Candidates.StoreSelectedClasses
open ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Render
open StoreDuplicateMetadata CombinedStoreOccurrences StoreOccurrenceIds HonestStoreRepresentatives

def selected (rs : List Occurrence) : List Occurrence :=
  rs.filter fun r=>r.eid==representativeId rs r.key

theorem selected_covers (rs : List Occurrence) (key : Key) :
    key∈(selected rs).map Occurrence.key ↔ key∈rs.map Occurrence.key := by
  constructor
  · intro h
    obtain ⟨r,hr,hk⟩:=List.mem_map.mp h
    exact List.mem_map.mpr ⟨r,(List.mem_filter.mp hr).1,hk⟩
  · intro h
    obtain ⟨r,hr,hk⟩:=List.mem_map.mp h
    obtain ⟨s,hs,hsk,hid⟩:=representative_found rs key ⟨r,hr,hk⟩
    apply List.mem_map.mpr
    refine ⟨s,List.mem_filter.mpr ⟨hs,?_⟩,hsk⟩
    simp [hsk,hid]

theorem selected_distinct (rs : List Occurrence) (hid : (rs.map Occurrence.eid).Nodup) :
    ((selected rs).map Occurrence.key).Nodup := by
  apply List.pairwise_map.mpr
  have hp : (selected rs).Pairwise (fun a b=>a.eid≠b.eid) :=
    (List.pairwise_map.mp hid).sublist List.filter_sublist
  apply List.Pairwise.imp_of_mem (p:=hp)
  intro a b ha hb hab hk
  have ha : a.eid=representativeId rs a.key := by simpa using (List.mem_filter.mp ha).2
  have hb : b.eid=representativeId rs b.key := by simpa using (List.mem_filter.mp hb).2
  exact hab (by rw [ha,hb,hk])

/-- The actual head/duplicate predicate selects exactly the distinct byte classes
used by the native store charge proof, with no missing or double-counted class. -/
theorem selected_classes (rs : List Occurrence) (hid : (rs.map Occurrence.eid).Nodup) :
    ((selected rs).map Occurrence.key).Perm (representatives (rs.map Occurrence.key)) := by
  apply (List.perm_ext_iff_of_nodup (selected_distinct rs hid) (distinct _)).mpr
  intro key
  rw [selected_covers,covers]

theorem selected_count (rs : List Occurrence) (hid : (rs.map Occurrence.eid).Nodup) :
    (selected rs).length=(representatives (rs.map Occurrence.key)).length := by
  have h:=(selected_classes rs hid).length_eq
  simpa only [List.length_map] using h

theorem selected_charge (rs : List Occurrence) (hid : (rs.map Occurrence.eid).Nodup) :
    charge ((selected rs).map Occurrence.key)=charge (representatives (rs.map Occurrence.key)) := by
  exact ((selected_classes rs hid).map (fun key=>key.2.length+4)).sum_nat

theorem node_ids (vs : List NodeS3) : ((nodeOccurrences vs).map Occurrence.eid).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [nodeOccurrences,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
  unfold eidN msgId
  omega

theorem value_ids (tau : ValE→Nat) (es : List ValE) (hv : ValWf es) :
    ((valueOccurrences tau es).map Occurrence.eid).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hi' : i<es.length := by simpa [valueOccurrences] using hi
  have hj' : j<es.length := by simpa [valueOccurrences] using hj
  simp only [valueOccurrences,List.getElem_map]
  change eidV es[i]≠eidV es[j]
  unfold eidV msgId
  rw [value_id es hv i hi',value_id es hv j hj']
  omega

theorem combined_ids (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) (hv : ValWf es) :
    ((allOccurrences vs tau es).map Occurrence.eid).Nodup := by
  rw [allOccurrences,List.map_append,List.nodup_append]
  refine ⟨node_ids vs,value_ids tau es hv,?_⟩
  intro a ha b hb he
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp ha
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hb
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hr
  obtain ⟨e,he',rfl⟩:=List.mem_map.mp hs
  exact StoreOccurrenceUnique.namespaces p.2 e.vid he
end ZkFormal.NearV3.Candidates.StoreSelectedClasses
