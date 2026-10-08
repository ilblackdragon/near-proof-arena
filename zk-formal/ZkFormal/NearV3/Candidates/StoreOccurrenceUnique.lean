import ZkFormal.NearV3.Candidates.StoreOccurrenceIds
namespace ZkFormal.NearV3.Candidates.StoreOccurrenceUnique
open ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Render
open StoreDuplicateMetadata CombinedStoreOccurrences StoreOccurrenceIds

/-- Node and value entity-ID namespaces are disjoint as natural IDs. -/
theorem namespaces (i j : Nat) : eidN i≠msgId K_VPRE j := by
  unfold eidN msgId K_NPRE K_VPRE
  omega

/-- A concrete entity ID identifies exactly one occurrence in the combined
list. Equal byte classes may repeat; their physical IDs cannot alias. -/
theorem entity_unique (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE) (hv : ValWf es)
    (a b : Occurrence) (ha : a∈allOccurrences vs tau es) (hb : b∈allOccurrences vs tau es)
    (he : a.eid=b.eid) : a=b := by
  rcases List.mem_append.mp ha with ha|ha <;> rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ha
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hb
    have hi : p.2=q.2 := by change eidN p.2=eidN q.2 at he; unfold eidN msgId at he; omega
    have hp':=List.mem_zipIdx_iff_getElem?.mp hp
    have hq':=List.mem_zipIdx_iff_getElem?.mp hq
    rw [hi] at hp'
    have hk : p.1=q.1 := Option.some.inj (hp'.symm.trans hq')
    simp only [hi,hk]
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ha
    obtain ⟨e,he',rfl⟩:=List.mem_map.mp hb
    exact False.elim (namespaces p.2 e.vid he)
  · obtain ⟨e,he',rfl⟩:=List.mem_map.mp ha
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hb
    exact False.elim (namespaces p.2 e.vid he.symm)
  · obtain ⟨e,he',rfl⟩:=List.mem_map.mp ha
    obtain ⟨f,hf',rfl⟩:=List.mem_map.mp hb
    obtain ⟨i,hi,hei⟩:=List.mem_iff_getElem.mp he'
    obtain ⟨j,hj,hfj⟩:=List.mem_iff_getElem.mp hf'
    subst e; subst f
    have hei:=value_id es hv i hi
    have hfj:=value_id es hv j hj
    have hij : i=j := by
      change eidV es[i]=eidV es[j] at he
      unfold eidV msgId at he
      rw [hei,hfj] at he
      omega
    subst j
    rfl

/-- If an occurrence carries its class representative ID, it is exactly the
actual selected representative, not a different record with an aliased ID. -/
theorem head_is_representative (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hv : ValWf es) (a : Occurrence) (ha : a∈allOccurrences vs tau es)
    (hh : a.eid=representativeId (allOccurrences vs tau es) a.key) :
    (allOccurrences vs tau es).find? (fun r=>r.key==a.key)=some a := by
  unfold representativeId at hh
  cases hf : (allOccurrences vs tau es).find? (fun r=>r.key==a.key) with
  | none =>
    exact False.elim ((List.find?_eq_none.mp hf) a ha (by simp))
  | some r =>
    have hr:=List.mem_of_find?_eq_some hf
    rw [hf] at hh
    have he : a=r := entity_unique vs tau es hv a r ha hr hh
    simpa [he]
end ZkFormal.NearV3.Candidates.StoreOccurrenceUnique
