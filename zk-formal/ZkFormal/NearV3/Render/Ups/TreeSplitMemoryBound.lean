import ZkFormal.NearV3.Render.Ups.TreeExtSplitMemory
import ZkFormal.NearV3.Render.Ups.MemGrowthTerminal

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Every scalar child-memory input used in a native leaf split fits the wide-carry budget. -/
theorem leafSplitRun_childMemory_bound (k key : List Nat) (old : Slot) (mem : Nat) (v : Bytes)
    (hw : (PTrie.leaf k old mem).wf=true) (hkey : key.length≤2) (hv : v.length<2^24) :
    ∀ part∈(leafSplitRun k old mem key v).parts,
      splitChildMemory (commonPrefix k key).length part<2^74 := by
  simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
  have hs : old.len<2^32 := by have hh := hw.1.1.2; cases old <;> simp_all [slotOk,Slot.len]
  have hk : k.length<2^34 := by rw [Render.NodeInfo.hexPrefix_len] at hw; omega
  have hp := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hp
  have hplen : (commonPrefix k key).length≤2 := by omega
  clear hp hw
  have hl : (k.drop (commonPrefix k key).length).length≤k.length := by simp only [List.length_drop]; omega
  have hr : (key.drop (commonPrefix k key).length).length≤key.length := by simp only [List.length_drop]; omega
  have hdrop : (k.drop ((commonPrefix k key).length+1)).length≤k.length := by simp only [List.length_drop]; omega
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
    simp only [h1,h2] <;> cases p <;>
    simp_all [wrapRun,terminalRun,pushPart,wrapExt,splitChildMemory,newLeaf,PTrie.memD,PTrie.mem?,
      leafMem,valueMem,extOwnMem,Render.NodeInfo.hexPrefix_len] <;>
    (repeat' (apply And.intro)) <;> omega

/-- The inherited memory is clamped natively, so source memory consistency is unnecessary. -/
theorem extSplitRun_childMemory_bound (k key : List Nat) (child : PTrie) (mem : Nat) (v : Bytes)
    (hw : (PTrie.ext k child mem).wf=true) (hkey : key.length≤2) (hv : v.length<2^24) :
    ∀ part∈(extSplitRun k child mem key v).parts,
      splitChildMemory (commonPrefix k key).length part<2^74 := by
  simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
  have hm := hw.1.2
  have hk : k.length<2^34 := by rw [Render.NodeInfo.hexPrefix_len] at hw; omega
  have hp := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hp
  have hplen : (commonPrefix k key).length≤2 := by omega
  clear hp hw
  have hl : (k.drop (commonPrefix k key).length).length≤k.length := by simp only [List.length_drop]; omega
  have hr : (key.drop (commonPrefix k key).length).length≤key.length := by simp only [List.length_drop]; omega
  have hdrop : (k.drop ((commonPrefix k key).length+1)).length≤k.length := by simp only [List.length_drop]; omega
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;>
      simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
      simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp_all [wrapRun,terminalRun,pushPart,wrapExt,splitChildMemory,newLeaf,PTrie.memD,PTrie.mem?,
        leafMem,valueMem,extOwnMem,Render.NodeInfo.hexPrefix_len] <;>
      (repeat' (apply And.intro)) <;> omega
end ZkFormal.NearV3.Render.UpsGen
