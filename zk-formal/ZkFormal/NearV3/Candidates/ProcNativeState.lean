import ZkFormal.NearV3.Candidates.ProcNativeGrant
namespace ZkFormal.NearV3.Candidates.ProcNativeState
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcNativeGrant
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def replay (n : Nat) (allowed : Array Bool) (reqs : List Req) (vs : List Nat) (st : St) : St :=
  vs.foldl (fun st v=>
    let q := reqs.toArray[v/64]!
    (tryGrant n allowed st q.link (q.incs.getD (v%64) 0)).2) st

theorem entries_inv (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hs : Inv n M s.2.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) : Inv n M out.2.1 :=
  ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z) (fun s=>Inv n M s.2.1)
    (fun v _ s hs out h=>ProcNativeGrant.entry_inv n M hM allowed reqs K z v s hs out h) s out hs h

/-- Executable native grant replay equals the complete successful model entry
loop, including its saturating-u64 semantics. -/
theorem entries_native (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (s out : ProcModelStep.EntryAcc)
    (hs : Inv n M s.2.1)
    (h : forIn vs s (ProcModelStep.entryStep n allowed reqs K z)=.ok out) :
    native out.2.1=replay n allowed reqs vs (native s.2.1) := by
  induction vs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; rfl
  | cons v vs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcModelStep.entryStep n allowed reqs K z v s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl,ht,hl⟩ := ProcModelEntryShape.entry_shape n allowed reqs K z v s next he
      simp only [he,bind,Except.bind] at h
      have hinv := ProcNativeGrant.entry_inv n M hM allowed reqs K z v s hs _ he
      have hg := ProcGrantAgreement.entry_grant n allowed reqs K z v s _ he
      simp only [ExceptLoop.StepInv] at hinv hg
      rw [ih next hinv h]
      change replay n allowed reqs vs (native next.2.1)=
        replay n allowed reqs vs (tryGrant n allowed (native s.2.1)
          reqs.toArray[v/64]!.link (reqs.toArray[v/64]!.incs.getD (v%64) 0)).2
      rw [grant_native n M hM allowed s.2.1 hs,hg]

set_option maxHeartbeats 800000 in
theorem step_inv (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (i : Nat) (s : ProcModelStep.Acc) (hs : Inv n M s.2.1)
    (out : ForInStep ProcModelStep.Acc) (h : ProcModelStep.step n allowed reqs i s=.ok out) :
    ExceptLoop.StepInv (fun s=>Inv n M s.2.1) out := by
  unfold ProcModelStep.step at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | rename_i sh rng hsh unused entryOut hentry
      exact entries_inv n M hM allowed reqs _ _ _ _ _ (by exact hs) hentry

set_option maxHeartbeats 400000 in
theorem process_inv (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round) (hs : Inv n M st0)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) : Inv n M st := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f
      (fun s : ProcModelStep.Acc=>Inv n M s.2.1) ?step ?b _ ?init ?loop
    case loop => assumption
    case init => exact hs
    case step => exact fun i _ s hs out h=>step_inv n M hM allowed reqs i s hs out h

theorem initial_process_bound (I : ZkFormal.NearV3.Sched.Gen.Input) (hn : 1≤I.ids.length)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (ha : I.allowed.size=I.ids.length*I.ids.length) (st : PState) (rs : List Round)
    (h : ProcCoreReplay.process I=.ok (st,rs)) : ∀l : Nat,st.g[l]!≤4500000 := by
  have hM : I.p.maxShardBandwidth≤u64Max := by rw [pv86_maxShard hp]; decide
  have hh := process_inv I.ids.length I.p.maxShardBandwidth hM I.allowed _ _ st _ rs
    (initial_inv I hn hp ha) h
  intro l
  have hg := hh l
  change st.g[l]!+st.sb[l/I.ids.length]!≤I.p.maxShardBandwidth at hg
  rw [pv86_maxShard hp] at hg
  omega
end ZkFormal.NearV3.Candidates.ProcNativeState
