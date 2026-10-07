import ZkFormal.NearV3.Render.Ups.TreeSplitMemoryInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

theorem leafSplitRun_matched (k : List Nat) (old : Slot) (mem : Nat) (key : List Nat) (v : Bytes)
    (hne : k≠key) : (leafSplitRun k old mem key v).matched=(commonPrefix k key).length := by
  have ho := commonPrefix_left k key
  have hp := commonPrefix_right k key
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;> simp only [h1,h2]
  · simp only [h1,h2,List.append_nil] at ho hp
    exact (hne (ho.trans hp.symm)).elim
  all_goals simp [wrapRun_matched,terminalRun]

theorem extSplitRun_matched (k : List Nat) (child : PTrie) (mem : Nat) (key : List Nat) (v : Bytes) :
    (extSplitRun k child mem key v).matched=(commonPrefix k key).length := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp [h1,h2,wrapRun_matched,terminalRun]
end ZkFormal.NearV3.Render.UpsGen
