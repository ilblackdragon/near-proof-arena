import ZkFormal.NearV3.Assembly.SchedulerStateSize
import ZkFormal.NearV3.Sched.Link.SoundPrep

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem scheduler_decode_hash_length {b : Bytes} {s : Bandwidth.State}
    (h : Bandwidth.State.decode b=some s) : s.sanityHash.length=32 := by
  unfold Bandwidth.State.decode at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hh
  split at h <;> try contradiction
  cases h
  exact Sched.takeN_length 32 _ _ _ hh

def schedulerSanityInput (pub : Scheduler.SchedPub) (prev : Option Bytes) : Option Bytes := do
  let old ← match prev with
    | none => some Bandwidth.State.initial
    | some b => Bandwidth.State.decode b
  some (old.sanityHash ++ pub.allShardsHash)

theorem schedPub_hash_length {ctx : ApplyCtx} {pub : Scheduler.SchedPub}
    (h : schedPub ctx=some pub) : pub.allShardsHash.length=32 := by
  unfold schedPub Scheduler.pubOf at h
  dsimp only at h
  split at h
  · simp [bind,Option.bind] at h
  · obtain ⟨p,_,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact ArenaCore.sha256_length _

theorem scheduler_core_sanity {pub : Scheduler.SchedPub} {prev : Option Bytes} {out : Scheduler.Output}
    (h : Scheduler.runCore pub prev=some out) (hh : pub.allShardsHash.length=32) :
    ∃ input, schedulerSanityInput pub prev=some input ∧ input.length=64 ∧
      ∃ links, out.state=(Bandwidth.State.mk links (sha256 input)).encode := by
  unfold Scheduler.runCore at h
  cases prev <;> dsimp only at h
  all_goals
    obtain ⟨old,hold,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st,_,h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst out
  · cases hold
    refine ⟨_,rfl,?_,_,rfl⟩
    simp [Bandwidth.State.initial,zeroHash,zeros,hh]
  · have hs := scheduler_decode_hash_length hold
    refine ⟨_,?_,?_,_,rfl⟩
    · simp [schedulerSanityInput,hold]
    · simp [List.length_append,hs,hh]

end ZkFormal.NearV3.Assembly
