import ZkFormal.NearV3.Candidates.ProcActualReplayKeyTrace
import ZkFormal.NearV3.Candidates.ProcActualReplayMemory
namespace ZkFormal.NearV3.Candidates.ProcActualReplayTimeEnvelope
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound
open ProcMemoryTimeInvariant

theorem stamped_time {T kp Kq zq : Nat} {rs : List Gen.RoundD}
    (h : ProcActualReplayChain.Stamped T kp Kq zq rs) : ∀rd∈rs,rd.T≤T := by
  induction h with
  | nil => simp
  | @snoc T kp Kq zq rs h K z L kend es ih =>
    intro rd hr
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with hr|rfl
    · exact Nat.le_trans (ih rd hr) (Nat.le_add_right T L)
    · exact Nat.le_add_right T L

theorem replay_round_times (B : Nat) (I : Input) (cv : Array CReq) (rs : List Round) (s : Acc)
    (hr : ProcActualReplayFactor.replay I cv rs=.ok s) (ht : time s<B) :
    ∀rd∈(ProcActualReplayKeyTrace.rounds s).toList,rd.T<B := by
  have hs := (ProcActualReplayKeyTrace.replay_metadata I cv rs s hr).1
  exact fun rd hm=>Nat.lt_of_le_of_lt (stamped_time hs rd hm) ht

theorem selected_time (t : Nat) (logs : Array (Array Gen.MOp))
    (h : AllBefore t logs) (i : Nat) : ∀o∈logs[i]!.toList,o.t<t := by
  by_cases hi : i<logs.size
  · rw [getElem!_pos logs i hi]
    exact (h logs[i] (by simpa using Array.getElem_mem hi)).2
  · rw [getElem!_neg logs i hi]
    change ∀o∈([] : List Gen.MOp),o.t<t
    simp

theorem memory_times (B : Nat) (s : Acc) (hm : ProcActualReplayMemory.Memory s)
    (ht : time s≤B) :
    (∀(i : Nat) (o : Gen.MOp),o∈s.2.2.2.2.1[i]!.toList → o.t<B) ∧
    (∀(i : Nat) (o : Gen.MOp),o∈s.2.2.2.2.2.1[i]!.toList → o.t<B) ∧
    (∀(i : Nat) (o : Gen.MOp),o∈s.2.2.2.2.2.2.1[i]!.toList → o.t<B) := by
  refine ⟨?_,?_,?_⟩
  · intro i o ho
    exact Nat.lt_of_lt_of_le (selected_time _ _ hm.1.1 i o ho) ht
  · intro i o ho
    exact Nat.lt_of_lt_of_le (selected_time _ _ hm.1.2.1 i o ho) ht
  · intro i o ho
    exact Nat.lt_of_lt_of_le (selected_time _ _ hm.1.2.2 i o ho) ht
end ZkFormal.NearV3.Candidates.ProcActualReplayTimeEnvelope
