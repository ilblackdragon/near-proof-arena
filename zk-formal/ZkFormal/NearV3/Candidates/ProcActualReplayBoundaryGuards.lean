import ZkFormal.NearV3.Candidates.ProcActualCoreReplay
import ZkFormal.NearV3.Candidates.ProcActualReplayRounds
import ZkFormal.NearV3.Candidates.ProcActualPreparedConversion
import ZkFormal.NearV3.Sched.Link.KeyPub
namespace ZkFormal.NearV3.Candidates.ProcActualReplayBoundaryGuards
open NearSpec NearSpecV3 ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

theorem rngAt_position (key : List Nat) (k : Nat) : rngPos (rngAt key k)=k := by
  unfold rngPos rngAt
  split <;> simp only [List.length_nil,List.length_drop,chachaBlock_length] <;> omega

theorem prepared_seed_guard {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (sp : Scheduler.SchedPub) (hsp : sp∈p.sched) :
    Gen.check ((leWords sp.seed).length==8) "seed length"=.ok () := by
  have hs := prepD0_seed hp sp hsp
  rw [leWords_eq 8 sp.seed (by omega)]
  simp [Gen.check,pure,Except.pure]

theorem model_final_rng_guard (I : Input) (st : PState) (rs : List Round)
    (h : ProcActualCoreReplay.process I=.ok (st,rs)) :
    ∃last,ProcActualReplayRounds.replayRounds (leWords I.seed) rs 0=.ok last ∧
      Gen.check (last==rngPos st.rng) "final RNG position differs"=.ok () := by
  obtain ⟨last,hr,hs⟩ := ProcActualReplayRounds.model_replay I st rs h
  exact ⟨last,hr,by simp [hs,rngAt_position,Gen.check,pure,Except.pure]⟩
end ZkFormal.NearV3.Candidates.ProcActualReplayBoundaryGuards
