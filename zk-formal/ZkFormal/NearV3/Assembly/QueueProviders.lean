import ZkFormal.NearV3.Assembly.ValueIndex
import ZkFormal.NearV3.Qv.ReadPlan

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

/-- Select each requested occurrence once; preserve native value ordinals. -/
def queueSelected (pre : PTrie) (rs : List ReadRequest) : List (Bytes × Nat) :=
  (NearSpecV3.valsOf pre).zipIdx.filter (fun x => rs.any (fun r => valueIndex pre r.key == some x.2))

def queueUsers (pre : PTrie) (rs : List ReadRequest) (i : Nat) : Nat :=
  rs.countP (fun r => valueIndex pre r.key == some i)

def queueRepresentative (pre : PTrie) (rs : List ReadRequest) (i : Nat) : ReadRequest :=
  (rs.find? (fun r => valueIndex pre r.key == some i)).getD ⟨[],none,.raw⟩

structure QueueProvider where
  tau : Nat
  vid : Nat
  bytes : Bytes
  mode : ParseMode
  users : Nat

def queueProviders (pre : PTrie) (rs : List ReadRequest) (tau base : Nat) : List QueueProvider :=
  (queueSelected pre rs).map (fun x =>
    ⟨tau,base+x.2,x.1,(queueRepresentative pre rs x.2).mode,queueUsers pre rs x.2⟩)

theorem queueSelected_mem {pre : PTrie} {rs : List ReadRequest} {b : Bytes} {i : Nat} :
    (b,i) ∈ queueSelected pre rs ↔
      (NearSpecV3.valsOf pre)[i]? = some b ∧ ∃ r ∈ rs, valueIndex pre r.key = some i := by
  simp only [queueSelected,List.mem_filter,List.mk_mem_zipIdx_iff_getElem?,List.any_eq_true,beq_iff_eq]

theorem queueSelected_complete {pre : PTrie} {rs : List ReadRequest} {r : ReadRequest}
    (hr : r ∈ rs) {b : Bytes} (hb : pre.find r.key = some (some b)) :
    ∃ i, valueIndex pre r.key = some i ∧ (b,i) ∈ queueSelected pre rs := by
  obtain ⟨i,hi,hget⟩ := valueIndex_complete pre r.key b hb
  exact ⟨i,hi,queueSelected_mem.mpr ⟨hget,r,hr,hi⟩⟩

theorem queueUsers_pos {pre : PTrie} {rs : List ReadRequest} {b : Bytes} {i : Nat}
    (h : (b,i) ∈ queueSelected pre rs) : 0 < queueUsers pre rs i := by
  obtain ⟨_,r,hr,hi⟩ := queueSelected_mem.mp h
  exact List.countP_pos_iff.mpr ⟨r,hr,by simpa using hi⟩

theorem queueUsers_bound (pre : PTrie) (rs : List ReadRequest) (i : Nat) :
    queueUsers pre rs i ≤ rs.length := List.countP_le_length

theorem queueRepresentative_spec {pre : PTrie} {rs : List ReadRequest} {b : Bytes} {i : Nat}
    (h : (b,i) ∈ queueSelected pre rs) :
    queueRepresentative pre rs i ∈ rs ∧ valueIndex pre (queueRepresentative pre rs i).key = some i := by
  obtain ⟨_,r,hr,hi⟩ := queueSelected_mem.mp h
  unfold queueRepresentative
  cases hf : rs.find? (fun r => valueIndex pre r.key == some i) with
  | none =>
    have hn := List.find?_eq_none.mp hf r hr
    simp [hi] at hn
  | some q =>
    simp only [Option.getD_some]
    exact ⟨List.mem_of_find?_eq_some hf,by simpa using List.find?_some hf⟩

theorem queueSelected_indices_nodup (pre : PTrie) (rs : List ReadRequest) :
    ((queueSelected pre rs).map Prod.snd).Nodup := by
  have hs := List.Sublist.map Prod.snd (List.filter_sublist
    (p := fun x : Bytes × Nat => rs.any (fun r => valueIndex pre r.key == some x.2))
    (l := (NearSpecV3.valsOf pre).zipIdx))
  apply List.Nodup.sublist hs
  simp [List.zipIdx_map_snd]
  exact List.nodup_range'

private theorem filter_weight_le {α : Type} (p : α → Bool) (weight : α → Nat) (xs : List α) :
    ((xs.filter p).map weight).sum ≤ (xs.map weight).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    by_cases hp : p x = true <;> simp [hp] <;> omega

theorem queueSelected_bytes (pre : PTrie) (rs : List ReadRequest) :
    ((queueSelected pre rs).map (fun x => x.1.length)).sum ≤
      ((NearSpecV3.valsOf pre).map List.length).sum := by
  have h := filter_weight_le (fun x : Bytes × Nat => rs.any (fun r => valueIndex pre r.key == some x.2))
    (fun x => x.1.length) (NearSpecV3.valsOf pre).zipIdx
  have he : ((NearSpecV3.valsOf pre).zipIdx.map fun x => x.1.length) =
      (NearSpecV3.valsOf pre).map List.length := by
    calc
      _ = (((NearSpecV3.valsOf pre).zipIdx).map Prod.fst).map List.length := (List.map_map ..).symm
      _ = _ := by rw [List.zipIdx_map_fst]
  rw [he] at h
  exact h

theorem queueProviders_bytes (pre : PTrie) (rs : List ReadRequest) (tau base : Nat) :
    ((queueProviders pre rs tau base).map (fun p => p.bytes.length)).sum ≤
      ((NearSpecV3.valsOf pre).map List.length).sum := by
  simpa only [queueProviders,List.map_map,Function.comp_def] using queueSelected_bytes pre rs

theorem queueProviders_owner {pre : PTrie} {rs : List ReadRequest} {tau base : Nat} {p : QueueProvider}
    (hp : p ∈ queueProviders pre rs tau base) : p.tau=tau ∧ base≤p.vid ∧
      p.vid < base+(NearSpecV3.valsOf pre).length ∧ 0<p.users ∧ p.users≤rs.length := by
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  have hb := (List.getElem?_eq_some_iff.mp (queueSelected_mem.mp hi).1).1
  have hu := queueUsers_pos hi
  have hl := queueUsers_bound pre rs i
  dsimp only
  exact ⟨rfl,by omega,by omega,hu,hl⟩

theorem queueProviders_ids_nodup (pre : PTrie) (rs : List ReadRequest) (tau base : Nat) :
    ((queueProviders pre rs tau base).map QueueProvider.vid).Nodup := by
  have hn := queueSelected_indices_nodup pre rs
  have hm := List.Pairwise.map (fun i => base+i) (fun a b h => by
    change base+a ≠ base+b
    omega) hn
  simpa only [queueProviders,List.map_map,Function.comp_def,List.Nodup] using hm

/-- Resolve a walk slot to its stable global value ID and exact request multiplicity. -/
def queueResolve (pre : PTrie) (rs : List ReadRequest) (base slot : Nat) : Nat × Nat :=
  ((valueIndex pre (rs.getD slot ⟨[],none,.raw⟩).key).map
    (fun i => (base+i,queueUsers pre rs i))).getD (0,0)

theorem queueResolve_present {pre : PTrie} {rs : List ReadRequest} {slot : Nat}
    {r : ReadRequest} (hr : rs[slot]? = some r) {b : Bytes}
    (hb : pre.find r.key = some (some b)) (tau base : Nat) :
    ∃ i, valueIndex pre r.key = some i ∧
      queueResolve pre rs base slot = (base+i,queueUsers pre rs i) ∧
      (⟨tau,base+i,b,(queueRepresentative pre rs i).mode,queueUsers pre rs i⟩ : QueueProvider)
        ∈ queueProviders pre rs tau base := by
  obtain ⟨i,hi,hs⟩ := queueSelected_complete (List.mem_of_getElem? hr) hb
  refine ⟨i,hi,?_,List.mem_map.mpr ⟨(b,i),hs,rfl⟩⟩
  simp [queueResolve,List.getD_eq_getElem?_getD,hr,hi]

theorem queueSelected_length (pre : PTrie) (rs : List ReadRequest) :
    (queueSelected pre rs).length ≤ rs.length := by
  have hsub : (queueSelected pre rs).map Prod.snd ⊆ rs.filterMap (fun r => valueIndex pre r.key) := by
    intro i hi
    obtain ⟨⟨b,j⟩,hj,rfl⟩ := List.mem_map.mp hi
    obtain ⟨_,r,hr,hidx⟩ := queueSelected_mem.mp hj
    exact List.mem_filterMap.mpr ⟨r,hr,hidx⟩
  have hh := List.Nodup.length_le_of_subset (queueSelected_indices_nodup pre rs) hsub
  simp only [List.length_map] at hh
  exact Nat.le_trans hh (List.length_filterMap_le ..)

theorem queueProviders_length (pre : PTrie) (rs : List ReadRequest) (tau base : Nat) :
    (queueProviders pre rs tau base).length ≤ rs.length := by
  simpa only [queueProviders,List.length_map] using queueSelected_length pre rs

end ZkFormal.NearV3.Assembly
