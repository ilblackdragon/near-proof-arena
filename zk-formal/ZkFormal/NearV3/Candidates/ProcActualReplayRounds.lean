import ZkFormal.NearV3.Candidates.ProcActualCoreReplay
import ZkFormal.NearV3.Candidates.ProcModelRng
namespace ZkFormal.NearV3.Candidates.ProcActualReplayRounds
open NearSpecV3 ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def replayRounds (key : List Nat) : List Round → Nat → Except String Nat
  | [],k => .ok k
  | rd::rs,k => do
    let (sh,k') ← replayShuffle key k (rd.bucket.map (·.v))
    Gen.check (sh==rd.shuffled) "shuffle replay differs"
    replayRounds key rs k'

theorem replay_append (key : List Nat) (xs ys : List Round) (k : Nat) :
    replayRounds key (xs++ys) k = (do
      let k' ← replayRounds key xs k
      replayRounds key ys k') := by
  induction xs generalizing k with
  | nil => rfl
  | cons rd xs ih =>
    simp only [List.cons_append,replayRounds]
    cases hs : replayShuffle key k (rd.bucket.map (·.v)) with
    | error e => simp [hs,bind,Except.bind]
    | ok pair =>
      rcases pair with ⟨sh,next⟩
      simp only [hs,bind,Except.bind]
      cases hc : Gen.check (sh==rd.shuffled) "shuffle replay differs" with
      | error e => simp [hc,bind,Except.bind]
      | ok u => simpa only [hc,bind,Except.bind] using ih next

theorem trace_replay (key : List Nat) (start : Nat) (rs : List Round) (last : Nat)
    (h : ProcModelRng.Trace key start rs last) : replayRounds key rs start=.ok last := by
  induction h with
  | nil => rfl
  | @snoc rs k ht rd last hs ih =>
    rw [replay_append,ih]
    simp only [bind,Except.bind,replayRounds,hs]
    simp [Gen.check,bind,Except.bind,pure,Except.pure]

theorem model_replay (I : Input) (st : PState) (rs : List Round)
    (h : ProcActualCoreReplay.process I=.ok (st,rs)) :
    ∃last,replayRounds (leWords I.seed) rs 0=.ok last ∧ st.rng=rngAt (leWords I.seed) last := by
  obtain ⟨last,hr,ht⟩ := ProcModelRng.process_trace I.ids.length I.allowed
    (convRaw I.p I.ids.length I.raw) (leWords I.seed) 0 (ProcActualCoreReplay.initial I) st _ rs
    (ofSeed_eq I.seed) h
  exact ⟨last,trace_replay _ _ _ _ ht,hr⟩
end ZkFormal.NearV3.Candidates.ProcActualReplayRounds
