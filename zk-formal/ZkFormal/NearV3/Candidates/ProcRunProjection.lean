import ZkFormal.NearV3.Sched.Gen.Run
namespace ZkFormal.NearV3.Candidates.ProcRunProjection
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
set_option maxHeartbeats 400000 in
theorem run_fields (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    R.tau=tau ∧ R.n=I.ids.length ∧ R.base=I.p.base ∧
    R.D=I.p.maxSingleGrant-I.p.base ∧ R.seed=I.seed ∧ R.key=NearSpecV3.leWords I.seed := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first
    | cases h
    | split at h
  all_goals exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
set_option maxHeartbeats 400000 in
theorem run_empty_raw (I : Input) (tau : Nat) (R : Run)
    (hraw : I.raw=[]) (h : Gen.run I tau=.ok R) : R.rounds=[] := by
  unfold Gen.run at h
  simp [hraw,List.forIn_nil,convRaw,processEv,bind,Except.bind,pure,Except.pure] at h
  repeat first
    | cases h
    | split at h
  all_goals rfl
set_option maxHeartbeats 400000 in
theorem run_params (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    I.p.base<2^24 ∧ I.p.maxSingleGrant-I.p.base<2^24 := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first
    | cases h
    | split at h
  all_goals
    have hc : check (I.p.base<2^24 && I.p.maxSingleGrant-I.p.base<2^24)
        "params ≥ 2^24"=.ok () := by assumption
    unfold check at hc
    split at hc
    · rename_i hh
      simpa using hh
    · cases hc

set_option maxHeartbeats 400000 in
theorem run_seed_words (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    (NearSpecV3.leWords I.seed).length=8 := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first
    | cases h
    | split at h
  all_goals
    have hc : check ((NearSpecV3.leWords I.seed).length==8) "seed length"=.ok () := by assumption
    unfold check at hc
    split at hc
    · rename_i hh
      simpa using hh
    · cases hc
end ZkFormal.NearV3.Candidates.ProcRunProjection
