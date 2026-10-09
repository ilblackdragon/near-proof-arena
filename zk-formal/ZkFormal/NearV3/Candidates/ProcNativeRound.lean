import ZkFormal.NearV3.Candidates.ProcRoundSuccess
namespace ZkFormal.NearV3.Candidates.ProcNativeRound
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcNativeGrant ProcNativePush
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def run (n : Nat) (allowed : Array Bool) (st : St) (bk : List (Nat×List Req)) :
    Option (St×List (Nat×List Req)) :=
  match NearSpecV3.shuffle bk.getLast!.2 st.rng with
  | none=>none
  | some (qs,rng)=>some (processBucket n allowed qs ({st with rng:=rng},bk.dropLast))

theorem shuffle_pullback {α β : Type} (f : α→β) (xs : List α) (r : NearSpecV3.Rng)
    (ys : List β) (r' : NearSpecV3.Rng) (h : NearSpecV3.shuffle (xs.map f) r=some (ys,r')) :
    ∃zs,NearSpecV3.shuffle xs r=some (zs,r') ∧ zs.map f=ys := by
  rw [shuffle_map] at h
  cases hs : NearSpecV3.shuffle xs r with
  | none => simp [hs] at h
  | some out =>
    rcases out with ⟨zs,rout⟩
    simp only [hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
    exact ⟨zs,by simpa [h.2] using hs,h.1⟩

theorem buckets_nonempty (reqs : List Req) (ps : List Push) (hn : ps≠[]) :
    bucketsOf reqs (ps.map toPM)≠[] := by
  obtain ⟨p,hp,hk⟩ := ProcMaxBucket.max_mem ps hn
  have hm : (toPM p).key∈keysOf (ps.map toPM) :=
    (mem_keysOf _ _).mpr ⟨toPM p,List.mem_map_of_mem hp,rfl⟩
  intro he
  rw [bucketsOf_eq_groups,groupsOf,List.map_eq_nil_iff] at he
  rw [he] at hm
  contradiction

set_option maxHeartbeats 1000000 in
/-- One successful event-model round is exactly one actual native bucket round,
including the native request shuffle and the updated bucket dictionary. -/
theorem step_refines (n M : Nat) (hM : M≤u64Max) (allowed : Array Bool) (reqs : List Req)
    (hr : ∀q∈reqs,q.incs.length<64) (i : Nat) (s out : ProcModelStep.Acc)
    (hn : s.1≠[]) (ht : s.1.Pairwise (fun p q=>p.ts<q.ts))
    (hv : ∀p∈s.1,ProcRequestPointers.Valid reqs p.v) (hg : Inv n M s.2.1)
    (h : ProcModelStep.step n allowed reqs i s=.ok (.yield out)) :
    run n allowed (native s.2.1) (bucketsOf reqs (s.1.map toPM))=
      some (native out.2.1,bucketsOf reqs (out.1.map toPM)) := by
  have hpop := ProcMaxBucket.native_pop reqs s.1 hn ht
  have hempty : s.1.isEmpty=false := by simpa using hn
  unfold ProcModelStep.step at h
  simp only [hempty,Bool.false_eq_true,ite_false,bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    rename_i sh rng hsh unused entryOut hentry
    have hvalid : ∀v∈sh,ProcRequestPointers.Valid reqs v := by
      intro v hm
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ((shuffle_perm hsh).mem_iff.mp hm)
      exact hv p (List.mem_filter.mp ((ProcPushPerm.sort_perm _).mem_iff.mp hp)).1
    have hb := ProcNativeBucketReplay.bucket_exact n M hM allowed reqs hr _ _ sh hvalid _ _ _ entryOut (by exact hg) hentry
    unfold run
    rw [hpop.1,hpop.2]
    have hm := shuffle_map (reqAt reqs)
      ((sortTs (s.1.filter (fun p=>p.key==ProcMaxBucket.maxKey s.1))).map (·.v)) s.2.1.rng
    dsimp only [ProcMaxBucket.maxKey] at hm ⊢
    rw [hsh] at hm
    simp only [Option.map_some,List.map_map,Function.comp_def] at hm
    dsimp only [native]
    rw [hm]
    exact congrArg some hb
end ZkFormal.NearV3.Candidates.ProcNativeRound
