import ZkFormal.NearV3.Candidates.ProcPriorWinner
namespace ZkFormal.NearV3.Candidates.ProcPriorSummary
open NearSpec NearSpecV3.Scheduler

def low (a : Nat) : Nat := a%16777216
def big (a : Nat) : Bool := decide (16777216≤a)
def increase (a fair : Nat) : Nat :=
  if big a then 4500000 else min (low a+fair) 4500000

theorem low_bound (a : Nat) : low a<16777216 := Nat.mod_lt _ (by decide)

/-- Only a low24 word and a nonzero-high flag need cross the allowance bus. -/
theorem increase_exact (a fair : Nat) :
    increase a fair=min (min (a+fair) u64Max) 4500000 := by
  unfold increase big low u64Max
  split
  next h =>
    have ha:16777216≤a := of_decide_eq_true h
    omega
  next h =>
    have ha:a<16777216 := by simpa using h
    rw [Nat.mod_eq_of_lt ha]
    omega

theorem same_summary (a b fair : Nat) (hl:low a=low b) (hb:big a=big b) :
    min (min (a+fair) u64Max) 4500000=min (min (b+fair) u64Max) 4500000 := by
  rw [←increase_exact,←increase_exact]
  simp only [increase,hl,hb]

/-- No allowance truncation is assumed, even for the maximal decoded u64. -/
theorem maximal_allowance : increase 18446744073709551615 2250000=4500000 := by
  decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorSummary
