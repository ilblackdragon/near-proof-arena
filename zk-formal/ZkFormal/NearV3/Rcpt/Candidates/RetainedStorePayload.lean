import ZkFormal.NearV3.Rcpt.Candidates.RetainedStoreCount

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly

/-- Natural weights preserve subset domination when retained representatives
are distinct. No positivity is required, so empty byte strings are included. -/
theorem nodup_weight_le {α : Type} (weight : α → Nat) {xs ys : List α}
    (hn : xs.Nodup) (hc : xs ⊆ ys) :
    (xs.map weight).sum ≤ (ys.map weight).sum := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hna, hnx⟩ := List.nodup_cons.mp hn
    have ha : a ∈ ys := hc (List.mem_cons_self ..)
    have hsub : xs ⊆ ys.erase a := by
      intro b hb
      have hba : b ≠ a := fun h => hna (h ▸ hb)
      exact (List.mem_erase_of_ne hba).2 (hc (List.mem_cons_of_mem _ hb))
    have hle := ih hnx hsub
    have he := ((List.perm_cons_erase ha).map weight).sum_nat
    simp only [List.map_cons,List.sum_cons] at he ⊢
    omega

private theorem erased_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a::xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp,erased_nodup _⟩
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)


private theorem weighted_flat {α β : Type} (xs : List α) (f : α → List β)
    (w : β → Nat) :
    ((xs.flatMap f).map w).sum=(xs.map fun a => ((f a).map w).sum).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

/-- Tagged byte ownership bounds retained payload, with multiplicity across
transition instances preserved. -/
theorem retained_payload_le (taus : List Nat) (store : Nat → List Bytes)
    (representatives : List (Nat×Bytes))
    (ht : taus.Nodup) (hs : ∀ tau∈taus,(store tau).Nodup)
    (hc : ∀ tau∈taus,∀ b∈store tau,(tau,b)∈representatives) :
    (taus.map fun tau => ((store tau).map List.length).sum).sum ≤
      (representatives.map fun p => p.2.length).sum := by
  have hn := taggedStores_nodup taus store ht hs
  have hsub : taggedStores taus store ⊆ representatives := by
    intro p hp
    obtain ⟨tau,hm,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact hc tau hm b hb
  have hh := nodup_weight_le (fun p : Nat×Bytes => p.2.length) hn hsub
  simpa only [taggedStores,weighted_flat,List.map_map,Function.comp_def] using hh

theorem ext_retained_payload_le (x : ExtV3) (taus : List Nat)
    (representatives : List (Nat×Bytes)) (ht : taus.Nodup)
    (hc : ∀ tau∈taus,∀ b∈x.rawStore tau,(tau,b)∈representatives) :
    (taus.map fun tau => ((x.store tau).map List.length).sum).sum ≤
      (representatives.map fun p => p.2.length).sum := by
  apply retained_payload_le taus x.store representatives ht
  · intro tau _
    exact erased_nodup _
  · intro tau hm b hb
    exact hc tau hm b (List.mem_eraseDups.mp hb)

theorem witness_payload_instances (k : WalkD0) (x : ExtV3) :
    witnessPayload (stateWitnessOfV3 k x)=
      ((List.range (k.implicitBlks.length+1)).map fun tau =>
        ((x.store tau).map List.length).sum).sum := by
  have hi : k.implicitBlks.zipIdx.map (fun p => ((x.store (p.2+1)).map List.length).sum)=
      (List.range k.implicitBlks.length).map (fun i => ((x.store (i+1)).map List.length).sum) := by
    calc
      _ = (k.implicitBlks.zipIdx.map Prod.snd).map
        (fun i => ((x.store (i+1)).map List.length).sum) := (List.map_map ..).symm
      _ = _ := by simp [List.zipIdx_map_snd,List.range_eq_range']
  simp only [witnessPayload,transitions,stateWitnessOfV3,List.map_cons,List.sum_cons,
    List.map_map,Function.comp_def,transitionPayload,ExtV3.transition,
    List.range_succ_eq_map,List.map_cons,List.sum_cons]
  exact congrArg (((x.store 0).map List.length).sum+·) (congrArg List.sum hi)

theorem native_witness_payload_le (k : WalkD0) (x : ExtV3)
    (representatives : List (Nat×Bytes))
    (hc : ∀ tau,tau≤k.implicitBlks.length → ∀ b∈x.rawStore tau,(tau,b)∈representatives) :
    witnessPayload (stateWitnessOfV3 k x)≤
      (representatives.map fun p => p.2.length).sum := by
  rw [witness_payload_instances]
  apply ext_retained_payload_le x _ representatives List.nodup_range
  intro tau ht b hb
  exact hc tau (by have hh := List.mem_range.mp ht; omega) b hb

end ZkFormal.NearV3.Rcpt.Candidates
