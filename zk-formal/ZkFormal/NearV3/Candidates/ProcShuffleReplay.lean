import ZkFormal.NearV3.Candidates.ProcCoreReplay
import ZkFormal.Chacha.RngSpec
namespace ZkFormal.NearV3.Candidates.ProcShuffleReplay
open NearSpecV3 ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def step (total : Nat) (key : List Nat) (i : Nat) (s : List Nat×Nat) :
    Except String (ForInStep (List Nat×Nat)) :=
  match genAt 64 (total-i+1) key s.2 with
  | none => .error "genAt fuel"
  | some (j,k') => .ok (.yield (swapAt s.1 (total-i) j,k'))

private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

theorem replay_eq (key : List Nat) (k : Nat) (vs : List Nat) :
    replayShuffle key k vs = (do
      let out ← forIn (List.range (vs.length-1)) (vs,k) (step (vs.length-1) key)
      return out) := by
  unfold replayShuffle ProcShuffleReplay.step
  simp only [throw_eq,bind,Except.bind,pure,Except.pure]
  split
  · rename_i he
    exact he.symm
  · rename_i out he
    cases out
    exact he.symm

theorem loop_replay (key : List Nat) (total : Nat) :
    ∀count start vs k result rng,
      start+count=total → shuffleLoop count vs (rngAt key k)=some (result,rng) →
      ∃last,forIn (List.range' start count) (vs,k) (step total key)=.ok (result,last) ∧
        rng=rngAt key last := by
  intro count
  induction count with
  | zero =>
    intro start vs k result rng hsum hs
    simp only [shuffleLoop,Option.some.injEq,Prod.mk.injEq] at hs
    rcases hs with ⟨rfl,rfl⟩
    exact ⟨k,rfl,rfl⟩
  | succ count ih =>
    intro start vs k result rng hsum hs
    simp only [shuffleLoop,genIndex_rngAt] at hs
    cases hg : genAt 64 (count+2) key k with
    | none => simp [hg] at hs
    | some pair =>
      rcases pair with ⟨j,k'⟩
      simp only [hg,Option.map_some] at hs
      obtain ⟨last,hl,hr⟩ := ih (start+1) (swapAt vs (count+1) j) k' result rng (by omega) hs
      refine ⟨last,?_,hr⟩
      have he : total-start=count+1 := by omega
      rw [List.range'_succ,List.forIn_cons]
      simpa only [step,he,Nat.add_assoc,hg,bind,Except.bind] using hl

/-- A successful native shuffle at the same stream position has an exact
successful generator replay; no additional rejection/fuel hypothesis. -/
theorem replay_of_shuffle (key : List Nat) (k : Nat) (vs result : List Nat) (rng : Rng)
    (h : shuffle vs (rngAt key k)=some (result,rng)) :
    ∃last,replayShuffle key k vs=.ok (result,last) ∧ rng=rngAt key last := by
  obtain ⟨last,hl,hr⟩ := loop_replay key (vs.length-1) (vs.length-1) 0 vs k result rng (by omega) h
  refine ⟨last,?_,hr⟩
  rw [replay_eq]
  simpa only [List.range_eq_range',bind,Except.bind,pure,Except.pure] using hl
end ZkFormal.NearV3.Candidates.ProcShuffleReplay
