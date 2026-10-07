import ZkFormal.NearV3.Assembly.QueuePartition
import ZkFormal.NearV3.Qv.Candidates.CombinedWordAggregate

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates Qv.Candidates.CombinedWalkGen

def queueCounterMsg (p : QueueProvider) (u : Nat) : List Nat :=
  [p.vid,p.tau,(queueRecord p).mode,u]

def providerWalks (ws : List Walk) (p : QueueProvider) : List Walk :=
  ws.filter (fun w => w.value.isSome && (w.tau==p.tau && w.vid==p.vid))

theorem providerWalks_ranks (ws : List Walk) (p : QueueProvider) :
    (providerWalks ws p).map Walk.users=providerWalkRanks ws p.tau p.vid := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : (w.value.isSome && (w.tau==p.tau && w.vid==p.vid))=true
    all_goals
      simp only [providerWalks,providerWalkRanks,List.filter_cons,List.filterMap_cons] at ih ⊢
      simp only [h,Bool.false_eq_true,ite_true,ite_false,List.map_cons,ih]

theorem providerWalks_messages (ws : List Walk) (p : QueueProvider) (sd : Bool)
    (hm : ∀ w ∈ providerWalks ws p, w.mode=(queueRecord p).mode) :
    (providerWalks ws p).flatMap (fun w => w.counterWordMessages sd) =
      (providerWalkRanks ws p.tau p.vid).map (fun u => queueCounterMsg p (if sd then u+1 else u)) := by
  rw [← providerWalks_ranks,List.map_map]
  have h : ∀ w ∈ providerWalks ws p,
      w.counterWordMessages sd=[queueCounterMsg p (if sd then w.users+1 else w.users)] := by
    intro w hw
    have hi := (List.mem_filter.mp hw).2
    simp only [Bool.and_eq_true,beq_iff_eq] at hi
    simp [Walk.counterWordMessages,hi.1,queueCounterMsg,hi.2.1,hi.2.2,hm w hw]
  calc
    _ = (providerWalks ws p).flatMap (fun w => [queueCounterMsg p (if sd then w.users+1 else w.users)]) := by
      unfold List.flatMap
      congr 1
      exact List.map_congr_left h
    _ = _ := (List.map_eq_flatMap).symm

theorem provider_counter_balance (ws : List Walk) (p : QueueProvider)
    (hr : providerWalkRanks ws p.tau p.vid=List.range' 0 p.users)
    (hm : ∀ w ∈ providerWalks ws p, w.mode=(queueRecord p).mode) :
    queueCounterMsg p 0 :: (providerWalks ws p).flatMap (fun w => w.counterWordMessages true) =
      (providerWalks ws p).flatMap (fun w => w.counterWordMessages false) ++ [queueCounterMsg p p.users] := by
  rw [providerWalks_messages ws p true hm,providerWalks_messages ws p false hm,hr]
  have h : 0 :: (List.range' 0 p.users).map (·+1)=List.range' 0 p.users ++ [p.users] := by
    rw [← List.range'_succ_left]
    simpa only [List.range'_succ,Nat.zero_add] using (List.range'_1_concat (s := 0) (n := p.users))
  have hh := congrArg (List.map (queueCounterMsg p)) h
  simpa [List.map_map,Function.comp_def] using hh

theorem plan_providerWalks_mode {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    {p : QueueProvider} (hp : p ∈ queueForestProviders 0 0 (queueInputs pre v pres)) :
    ∀ w ∈ providerWalks (plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)) p,
      w.mode=(queueRecord p).mode := by
  intro w hw
  obtain ⟨hw,hsel⟩ := List.mem_filter.mp hw
  simp only [Bool.and_eq_true,beq_iff_eq] at hsel
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp hsel.1
  obtain ⟨q,hq,_,_,hvid,_,hmode⟩ := plan_rank_provider_mode hh hw hb
  have he : q=p := nodup_key_eq _ QueueProvider.vid
    (queueForestProviders_ids_nodup _ 0 0) hq hp (hvid.symm.trans hsel.2.2)
  subst q
  exact hmode.symm

/-- Actual full-plan counter messages balance with both parser endpoints for
 each concrete provider, including the mode field. -/
theorem plan_provider_counter_balance {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    {p : QueueProvider} (hp : p ∈ queueForestProviders 0 0 (queueInputs pre v pres)) :
    let ws := plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)
    queueCounterMsg p 0 :: (providerWalks ws p).flatMap (fun w => w.counterWordMessages true) =
      (providerWalks ws p).flatMap (fun w => w.counterWordMessages false) ++ [queueCounterMsg p p.users] := by
  apply provider_counter_balance
  · exact plan_provider_counter_class pres (hh (pre,mainRequests pre v) (by simp [queueInputs])) hp
  · exact plan_providerWalks_mode pres hh hp

end ZkFormal.NearV3.Assembly
