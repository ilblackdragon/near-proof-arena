import ZkFormal.NearV3.Assembly.QueueShardBalance

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Render.UpsGen

theorem seedValuesFrom_zipIdx (base : Nat) (bs : List Bytes) :
    seedValuesFrom base bs=bs.zipIdx.map (fun (b,i) => seedValue (base+i) b) := by
  induction bs generalizing base with
  | nil => rfl
  | cons b bs ih =>
    rw [List.zipIdx_cons']
    simp [seedValuesFrom,ih,List.map_map,Function.comp_def,Prod.map,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem queueProviders_seed_sublist (pre : PTrie) (rs : List ReadRequest) (tau base : Nat) :
    ((queueProviders pre rs tau base).map (fun p => seedValue p.vid p.bytes)).Sublist
      (seedValuesFrom base (valsOf pre)) := by
  rw [seedValuesFrom_zipIdx]
  have h := (List.filter_sublist (p := fun x : Bytes × Nat =>
    rs.any (fun r => valueIndex pre r.key == some x.2)) (l := (NearSpecV3.valsOf pre).zipIdx)).map
      (fun x => seedValue (base+x.2) x.1)
  simpa only [queueProviders,queueSelected,List.map_map,Function.comp_def,native_valsOf_eq] using h

theorem queueForestProviders_seed_sublist : ∀ xs tau base,
    ((queueForestProviders tau base xs).map (fun p => seedValue p.vid p.bytes)).Sublist
      (seedValuesFrom base (forestBytes (xs.map Prod.fst)))
  | [],_,_ => .slnil
  | (pre,rs)::rest,tau,base => by
    simp only [queueForestProviders,List.map_append,List.map_cons,forestBytes,List.flatMap_cons,
      seedValuesFrom_append,native_valsOf_eq]
    exact (queueProviders_seed_sublist pre rs tau base).append
      (queueForestProviders_seed_sublist rest (tau+1) (base+(valsOf pre).length))

theorem sublist_flatMap {α β : Type} (f : α → List β) {xs ys : List α}
    (h : xs.Sublist ys) : (xs.flatMap f).Sublist (ys.flatMap f) := by
  induction h with
  | slnil => exact .slnil
  | cons a h ih => exact ih.trans (List.sublist_append_right ..)
  | cons_cons a h ih => exact (List.Sublist.refl (f a)).append ih

end ZkFormal.NearV3.Assembly
