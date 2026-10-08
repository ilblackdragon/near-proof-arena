import ZkFormal.NearV3.Rcpt.Candidates.NativeWitnessCharge
import ZkFormal.NearV3.Assembly.Witness

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly

private theorem erased_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a::xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp,erased_nodup _⟩
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

def taggedStores (taus : List Nat) (store : Nat → List Bytes) : List (Nat×Bytes) :=
  taus.flatMap fun tau => (store tau).map fun b => (tau,b)

/-- Per-transition byte deduplication must retain the transition tag: equal bytes
in distinct transition instances are separate native vector records. -/
theorem taggedStores_nodup (taus : List Nat) (store : Nat → List Bytes)
    (ht : taus.Nodup) (hs : ∀ tau∈taus,(store tau).Nodup) :
    (taggedStores taus store).Nodup := by
  induction taus with
  | nil => simp [taggedStores]
  | cons t ts ih =>
    obtain ⟨htn,htt⟩ := List.nodup_cons.mp ht
    have hh := hs t (by simp)
    have hi := ih htt (fun tau hm => hs tau (by simp [hm]))
    simp only [taggedStores,List.flatMap_cons,List.nodup_append]
    refine ⟨?_,hi,?_⟩
    · apply List.pairwise_map.mpr
      exact hh.imp (fun h he => h (Prod.mk.inj he).2)
    · intro p hp q hq heq
      subst q
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
      obtain ⟨tau,hm,hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨c,hc,he⟩ := List.mem_map.mp hq
      have heq := (Prod.mk.inj he).1
      exact htn (heq ▸ hm)

/-- Covering retained tagged bytes by counted representatives suffices for the
private prefix charge, including empty values and shared node/value bytes. -/
theorem retained_count_le (taus : List Nat) (store : Nat → List Bytes)
    (representatives : List (Nat×Bytes))
    (ht : taus.Nodup) (hs : ∀ tau∈taus,(store tau).Nodup)
    (hc : ∀ tau∈taus,∀ b∈store tau,(tau,b)∈representatives) :
    (taus.map fun tau => (store tau).length).sum≤representatives.length := by
  have hn := taggedStores_nodup taus store ht hs
  have hsub : ∀ p∈taggedStores taus store,p∈representatives := by
    intro p hp
    obtain ⟨tau,hm,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact hc tau hm b hb
  have hh := List.Nodup.length_le_of_subset hn hsub
  simpa only [taggedStores,List.length_flatMap,List.length_map] using hh

/-- Applied to the actual executable witness stores; representative coverage is
an explicit global uniqueness/ownership obligation, not inferred from counts. -/
theorem ext_retained_count_le (x : ExtV3) (taus : List Nat)
    (representatives : List (Nat×Bytes)) (ht : taus.Nodup)
    (hc : ∀ tau∈taus,∀ b∈x.rawStore tau,(tau,b)∈representatives) :
    (taus.map fun tau => (x.store tau).length).sum≤representatives.length := by
  apply retained_count_le taus x.store representatives ht
  · intro tau _
    exact erased_nodup _
  · intro tau hm b hb
    exact hc tau hm b (List.mem_eraseDups.mp hb)

/-- Exact set of native transition instances, including the main transition. -/
theorem witness_record_instances (k : WalkD0) (x : ExtV3) :
    witnessRecordCount (stateWitnessOfV3 k x)=
      ((List.range (k.implicitBlks.length+1)).map fun tau => (x.store tau).length).sum := by
  have hi : k.implicitBlks.zipIdx.map (fun p => (x.store (p.2+1)).length)=
      (List.range k.implicitBlks.length).map (fun i => (x.store (i+1)).length) := by
    calc
      _ = (k.implicitBlks.zipIdx.map Prod.snd).map (fun i => (x.store (i+1)).length) :=
        (List.map_map ..).symm
      _ = _ := by simp [List.zipIdx_map_snd,List.range_eq_range']
  simp only [witnessRecordCount,transitions,stateWitnessOfV3,List.map_cons,List.sum_cons,
    List.map_map,Function.comp_def,transitionRecordCount,ExtV3.transition,
    List.range_succ_eq_map,List.map_cons,List.sum_cons]
  exact congrArg ((x.store 0).length+·) (congrArg List.sum hi)

/-- Native witness count domination with no independent count assumption: only
coverage by the globally counted, instance-tagged representatives remains. -/
theorem native_witness_count_le (k : WalkD0) (x : ExtV3)
    (representatives : List (Nat×Bytes))
    (hc : ∀ tau,tau≤k.implicitBlks.length → ∀ b∈x.rawStore tau,(tau,b)∈representatives) :
    witnessRecordCount (stateWitnessOfV3 k x)≤representatives.length := by
  rw [witness_record_instances]
  apply ext_retained_count_le x _ representatives List.nodup_range
  intro tau ht b hb
  exact hc tau (by have hh := List.mem_range.mp ht; omega) b hb

end ZkFormal.NearV3.Rcpt.Candidates
