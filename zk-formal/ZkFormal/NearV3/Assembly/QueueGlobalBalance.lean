import ZkFormal.NearV3.Assembly.QueueCounterMessages

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates Qv.Candidates.CombinedWalkGen

private theorem present_messages (ws : List Walk) (sd : Bool) :
    ws.flatMap (fun w => w.counterWordMessages sd)=
      (ws.filter (fun w => w.value.isSome)).flatMap (fun w => w.counterWordMessages sd) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases hv : w.value.isSome <;> simp [Walk.counterWordMessages,hv] <;> exact ih

theorem plan_walk_partition {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1) :
    let ws := plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)
    let ps := queueForestProviders 0 0 (queueInputs pre v pres)
    (ws.filter (fun w => w.value.isSome)).Perm (ps.flatMap (providerWalks ws)) := by
  classical
  dsimp only
  let ws := plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)
  let ps := queueForestProviders 0 0 (queueInputs pre v pres)
  have hc : ∀ w ∈ ws.filter (fun w => w.value.isSome), w.vid ∈ ps.map QueueProvider.vid := by
    intro w hw
    obtain ⟨hw,hv⟩ := List.mem_filter.mp hw
    obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp hv
    obtain ⟨p,hp,_,_,hvid,_,_⟩ := plan_rank_provider_mode hh hw hb
    exact List.mem_map.mpr ⟨p,hp,hvid.symm⟩
  have he : ∀ p ∈ ps,
      (ws.filter (fun w => w.value.isSome)).filter (fun w => w.vid==p.vid)=providerWalks ws p := by
    intro p hp
    rw [List.filter_filter]
    apply List.filter_congr
    intro w hw
    by_cases hv : w.value.isSome=true
    · obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp hv
      obtain ⟨q,hq,ht,_,hvid,_,_⟩ := plan_rank_provider_mode hh hw hb
      by_cases hid : w.vid=p.vid
      · have hqp := nodup_key_eq ps QueueProvider.vid (queueForestProviders_ids_nodup _ 0 0)
          hq hp (hvid.symm.trans hid)
        subst q
        simp [hv,hid,ht]
      · apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true,beq_iff_eq]
        simp only [hid,false_and,and_false]
    · simp [hv]
  have h := provider_partition (ws.filter (fun w => w.value.isSome)) ps Walk.vid QueueProvider.vid
    (queueForestProviders_ids_nodup _ 0 0) hc
  have hg : ps.flatMap (fun p => (ws.filter (fun w => w.value.isSome)).filter (fun w => w.vid==p.vid)) =
      ps.flatMap (providerWalks ws) := by
    unfold List.flatMap
    congr 1
    exact List.map_congr_left he
  exact hg ▸ h

private theorem flatMap_append_perm {α β : Type} (xs : List α) (f g : α → List β) :
    (xs.flatMap f ++ xs.flatMap g).Perm (xs.flatMap (fun x => f x ++ g x)) := by
  classical
  apply List.perm_iff_count.mpr
  intro b
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.count_append] at ih ⊢
    omega

private theorem flatMap_perm_mem {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, (f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact (h x (by simp)).append (ih (fun y hy => h y (by simp [hy])))

/-- Exact logical QVC balance for the corrected full native queue plan. -/
theorem plan_qvc_balance {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1) :
    let ws := plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)
    let ps := queueForestProviders 0 0 (queueInputs pre v pres)
    (ws.flatMap (fun w => w.counterWordMessages true) ++ ps.map (fun p => queueCounterMsg p 0)).Perm
      (ws.flatMap (fun w => w.counterWordMessages false) ++ ps.map (fun p => queueCounterMsg p p.users)) := by
  dsimp only
  let ws := plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)
  let ps := queueForestProviders 0 0 (queueInputs pre v pres)
  let send := fun p => (providerWalks ws p).flatMap (fun w => w.counterWordMessages true)
  let recv := fun p => (providerWalks ws p).flatMap (fun w => w.counterWordMessages false)
  have hg (sd : Bool) : (ws.flatMap (fun w => w.counterWordMessages sd)).Perm
      (ps.flatMap (fun p => (providerWalks ws p).flatMap (fun w => w.counterWordMessages sd))) := by
    rw [present_messages]
    have h := List.Perm.flatMap_right (fun w => w.counterWordMessages sd) (plan_walk_partition pres hh)
    simpa only [List.flatMap_assoc] using h
  have he : (ps.flatMap (fun p => send p ++ [queueCounterMsg p 0])).Perm
      (ps.flatMap (fun p => recv p ++ [queueCounterMsg p p.users])) := by
    apply flatMap_perm_mem
    intro p hp
    have h := plan_provider_counter_balance pres hh hp
    exact (List.perm_append_comm).trans (List.Perm.of_eq h)
  calc
    List.Perm _ (ps.flatMap send ++ ps.map (fun p => queueCounterMsg p 0)) := (hg true).append_right _
    List.Perm _ (ps.flatMap (fun p => send p ++ [queueCounterMsg p 0])) := by
      rw [List.map_eq_flatMap]
      exact flatMap_append_perm ps send _
    List.Perm _ (ps.flatMap (fun p => recv p ++ [queueCounterMsg p p.users])) := he
    List.Perm _ (ps.flatMap recv ++ ps.map (fun p => queueCounterMsg p p.users)) := by
      rw [List.map_eq_flatMap]
      exact (flatMap_append_perm ps recv _).symm
    List.Perm _ _ := (hg false).symm.append_right _

end ZkFormal.NearV3.Assembly
