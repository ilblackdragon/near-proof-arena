import ZkFormal.NearV3.Candidates.ProcReplayTimestampPotential
namespace ZkFormal.NearV3.Candidates.ProcReplayTimestampRounds
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcRequestPointers ProcReplayTimestampPotential
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def Inv (reqs : List Req) (B : Nat) (s : ProcModelStep.Acc) : Prop :=
  ProcModelPointers.Inv reqs s ∧ charge s.1+s.2.2.1≤B

set_option maxHeartbeats 800000 in
theorem step_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hsmall:Small reqs) (B i : Nat) (s : ProcModelStep.Acc) (hs:Inv reqs B s)
    (out : ForInStep ProcModelStep.Acc) (h:ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (Inv reqs B) out := by
  have hp:=ProcModelPointers.step_inv n allowed reqs hsmall i s hs.1 out h
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      have hv:∀v∈sh,Valid reqs v := by
        intro v hv
        have hm := (shuffle_perm hsh).mem_iff.mp hv
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
        have hp' := (ProcPushPerm.sort_perm _).mem_iff.mp hp
        exact hs.1.1 p (List.mem_filter.mp hp').1
      have he:=entries_charge n allowed reqs _ _ sh _ entryOut hsmall hv hentry
      have hweight: (sh.map weight).sum =
          charge (sortTs (s.1.filter (·.key == s.1.foldl (fun m p=>Nat.max m p.key) 0))) := by
        have hh:=((shuffle_perm hsh).map weight).sum_nat
        simpa only [List.map_map,Function.comp_def,charge] using hh
      have hpart:=((ProcPushPerm.pop_perm s.1 (s.1.foldl (fun m p=>Nat.max m p.key) 0)).map (fun p=>weight p.v)).sum_nat
      simp only [List.map_append,List.sum_append] at hpart
      change charge (s.1.filter _) + charge (sortTs (s.1.filter _)) = charge s.1 at hpart
      refine ⟨hp,?_⟩
      change charge entryOut.1+entryOut.2.2.1≤B
      rw [hweight] at he
      have hb:=hs.2
      dsimp only at he
      omega
theorem charge_le (ps : List Push) : charge ps≤64*ps.length := by
  induction ps with
  | nil => simp [charge]
  | cons p ps ih =>
    simp only [charge,List.map_cons,List.sum_cons,List.length_cons] at *
    have hh:weight p.v≤64 := Nat.sub_le _ _
    omega

theorem initial_bound (reqs : List Req) (st0 : PState) :
    Inv reqs (65*reqs.length) (ProcModelStep.initial reqs st0) := by
  refine ⟨⟨initial_valid reqs st0,by simp [ProcModelStep.initial]⟩,?_⟩
  have hc:=charge_le (ProcModelStep.initial reqs st0).1
  have hl:(ProcModelStep.initial reqs st0).1.length≤reqs.length := by
    unfold ProcModelStep.initial
    dsimp only
    exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)
  change charge (ProcModelStep.initial reqs st0).1+reqs.length≤65*reqs.length
  omega

set_option maxHeartbeats 400000 in
/-- Request pointers pay for every processed entry; this bound is independent
of replay success and of the number of model rounds. -/
theorem process_entries_bound (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hs:Small reqs) (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h:processEv n allowed reqs st0 fuel=.ok (st,rs)) :
    (rs.flatMap Round.steps).length≤64*reqs.length := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh:Inv reqs (65*reqs.length) ?out := by
      refine ExceptLoop.invariant (α:=Nat) (ε:=String) ?xs ?f (Inv reqs (65*reqs.length)) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact initial_bound reqs st0
      case step => exact fun i _ s hs0 out h=>step_inv n allowed reqs hs _ i s hs0 out h
    have ht:ProcModelRoundShape.Inv reqs.length ?out := by
      refine ExceptLoop.invariant (α:=Nat) (ε:=String) ?xs ?f (ProcModelRoundShape.Inv reqs.length) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact ProcModelRoundShape.Trace.nil
      case step => exact fun i _ s hs0 out h=>ProcModelRoundShape.step_inv n allowed reqs reqs.length i s hs0 out h
    have he:=(ProcModelClock.trace_flat ht).1
    have hb:=hh.2
    omega
end ZkFormal.NearV3.Candidates.ProcReplayTimestampRounds

