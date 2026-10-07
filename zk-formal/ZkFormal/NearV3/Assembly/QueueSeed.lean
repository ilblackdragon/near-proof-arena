import ZkFormal.NearV3.Assembly.QueueForest
import ZkFormal.NearV3.Assembly.ForestViews

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
theorem native_occs_eq : ∀ t : PTrie, NearSpecV3.occs t = occs t
  | .hash _ => rfl
  | .leaf _ _ _ => rfl
  | .ext _ c _ => by simp [NearSpecV3.occs,occs,native_occs_eq c]
  | .branch _ cs _ => by simp [NearSpecV3.occs,occs,native_kOccs_eq cs]
theorem native_kOccs_eq : ∀ cs : Kids, NearSpecV3.kOccs cs = kOccs cs
  | .nil => rfl
  | .none cs => by simp [NearSpecV3.kOccs,kOccs,native_kOccs_eq cs]
  | .some c cs => by simp [NearSpecV3.kOccs,kOccs,native_occs_eq c,native_kOccs_eq cs]
end

theorem native_ownVals_eq (t : PTrie) : NearSpecV3.ownVals t = ownVals t := by
  cases t with
  | hash _ => rfl
  | ext _ _ _ => rfl
  | leaf k v m => cases v <;> rfl
  | branch v cs m => cases v with
    | none => rfl
    | some v => cases v <;> rfl

theorem native_valsOf_eq (t : PTrie) : NearSpecV3.valsOf t = valsOf t := by
  simp only [NearSpecV3.valsOf,valsOf,native_occs_eq]
  congr 1

theorem seedValuesFrom_get (base : Nat) (bs : List Bytes) (i : Nat) (b : Bytes)
    (h : bs[i]? = some b) :
    (seedValuesFrom base bs)[i]? = some (seedValue (base+i) b) := by
  induction bs generalizing base i with
  | nil => simp at h
  | cons a bs ih =>
    cases i with
    | zero => simp at h; subst b; simp [seedValuesFrom]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simpa [seedValuesFrom,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (base+1) i h

/-- A requested native occurrence uses its existing seeded value record. -/
theorem queueProviders_seed {pre : PTrie} {rs : List Qv.ReadRequest} {tau base : Nat} (nid : Nat)
    {p : QueueProvider} (hp : p ∈ queueProviders pre rs tau base) :
    seedValue p.vid p.bytes ∈ seedValuesFrom base (valsOf pre) ∧
      Link3.valTau (seedNodesT tau 0 nid base pre) p.vid = p.tau := by
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  have hg := (queueSelected_mem.mp hi).1
  rw [native_valsOf_eq] at hg
  constructor
  · exact List.mem_of_getElem? (seedValuesFrom_get base (valsOf pre) i b hg)
  · apply seedNodesT_valTau
    have hb := (List.getElem?_eq_some_iff.mp hg).1
    simp only [List.mem_range']
    exact ⟨i,hb,by omega⟩

/-- Queue providers preserve the global value address and its native instance. -/
theorem queueForestProviders_seed : ∀ xs tau nid base (p : QueueProvider),
    p ∈ queueForestProviders tau base xs →
    seedValue p.vid p.bytes ∈ seedValuesFrom base (forestBytes (xs.map Prod.fst)) ∧
    Link3.valTau (forestNodes tau nid base (xs.map Prod.fst)) p.vid = p.tau
  | [],_,_,_,_,h => by simp [queueForestProviders] at h
  | (pre,rs)::rest,tau,nid,base,p,h => by
    simp only [queueForestProviders,List.mem_append] at h
    simp only [List.map_cons,forestBytes,List.flatMap_cons,seedValuesFrom_append,forestNodes]
    rcases h with h | h
    · obtain ⟨hm,ht⟩ := queueProviders_seed nid h
      refine ⟨List.mem_append_left _ hm,?_⟩
      rw [valTau_append_left]
      · exact ht
      · rw [seedNodesT_valueIds]
        have hb := queueProviders_owner h
        rw [native_valsOf_eq] at hb
        simp only [List.mem_range']
        exact ⟨p.vid-base,by omega,by omega⟩
    · rw [native_valsOf_eq] at h
      obtain ⟨hm,ht⟩ := queueForestProviders_seed rest (tau+1) (nid+tsize pre)
        (base+(valsOf pre).length) p h
      refine ⟨List.mem_append_right _ hm,?_⟩
      rw [valTau_append_right]
      · exact ht
      · rw [seedNodesT_valueIds]
        intro hi
        have hb := queueForestProviders_bounds rest (tau+1) (base+(valsOf pre).length) h
        simp only [List.mem_range'] at hi
        obtain ⟨i,hi,he⟩ := hi
        omega

theorem queueForestProviders_store_seed (xs : List (PTrie × List Qv.ReadRequest))
    (p : QueueProvider) (hp : p ∈ queueForestProviders 0 0 xs) :
    seedValue p.vid p.bytes ∈ (forestStoreViews (xs.map Prod.fst)).values ∧
    Link3.valTau (forestStoreViews (xs.map Prod.fst)).nodes p.vid = p.tau :=
  queueForestProviders_seed xs 0 0 0 p hp

end ZkFormal.NearV3.Assembly
