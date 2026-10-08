import ZkFormal.NearV3.Candidates.CombinedStoreOccurrences
namespace ZkFormal.NearV3.Candidates.StoreOccurrenceIds
open ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Render
open StoreDuplicateMetadata CombinedStoreOccurrences

/-- Empty values occupy a physical row too, so all value IDs fit the row cap. -/
theorem value_length (es : List ValE) (h : ValWf es) : es.length<2^22 := by
  have hp : ∀e∈es,1≤ValGen.nOf e := by
    intro e he
    have hh:=h.shape e he
    cases hv : e.vz with
    | true => simp [ValGen.nOf,hv]
    | false => have hh:=hh.2 hv; simp [ValGen.nOf,hv]; omega
  have hs : es.length≤(es.map ValGen.nOf).sum := by
    clear h
    induction es with
    | nil => simp
    | cons e es ih =>
      have he:=hp e (by simp)
      have ht:=ih (fun e he=>hp e (by simp [he]))
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
  have hr:=h.rows
  change (es.map ValGen.nOf).sum+1≤2^22 at hr
  omega

/-- Consecutive native value IDs are actual natural indices, not merely field
residues: the existing physical row cap excludes wraparound. -/
theorem value_id (es : List ValE) (h : ValWf es) (i : Nat) (hi : i<es.length) :
    es[i].vid=i := by
  induction i with
  | zero => exact h.first hi
  | succ i ih =>
    have hp : i<es.length := by omega
    rw [h.ids i hi,ih hp]
    apply Nat.mod_eq_of_lt
    have hl:=value_length es h
    unfold ZkFormal.Algebra.P
    omega

theorem entity_ids_small (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : NodeWf3 vs) (hv : ValWf es) :
    ∀r∈allOccurrences vs tau es,r.eid<P := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hr
    have hi:=List.snd_lt_of_mem_zipIdx hp
    have hc:=hn.count
    change eidN p.2<P
    unfold eidN msgId K_NPRE ZkFormal.Algebra.P
    omega
  · obtain ⟨e,he,rfl⟩:=List.mem_map.mp hr
    obtain ⟨i,hi,hei⟩:=List.mem_iff_getElem.mp he
    subst e
    have hid:=value_id es hv i hi
    have hl:=value_length es hv
    change eidV es[i]<P
    unfold eidV msgId K_VPRE
    rw [hid]
    unfold ZkFormal.Algebra.P
    omega

/-- Canonical representative entity IDs follow from the same local native
views; they are no longer an extra premise of duplicate metadata assignment. -/
theorem assigned_wf (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : NodeWf3 vs) (hv : ValWf es) :
    NodeWf3 (assign (allOccurrences vs tau es) 0 vs) ∧
    ValWf (ValueDuplicateMetadata.assign (allOccurrences vs tau es) tau es) :=
  CombinedStoreOccurrences.assigned_wf vs tau es hn hv (entity_ids_small vs tau es hn hv)
end ZkFormal.NearV3.Candidates.StoreOccurrenceIds
