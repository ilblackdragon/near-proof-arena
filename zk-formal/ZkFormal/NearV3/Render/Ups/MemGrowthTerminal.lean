import ZkFormal.NearV3.Render.Ups.TreeMemoryInput
import ZkFormal.NearV3.Render.Ups.TreePartCount

/-! Coarse exact-memory growth bounds use native structural well-formedness,
not parent/child memory consistency or a bound on newly computed u64 totals. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

private theorem commonPrefix_key_bound (k key : List Nat) (hk : key.length≤2) :
    (commonPrefix k key).length≤2 := by
  have h := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append,List.length_drop] at h
  omega

theorem splitLeaf_memory_bound (k key : List Nat) (s : Slot) (v : Bytes)
    (hkey : key.length≤2) (hk : k.length<2^34) (hs : s.len<2^32) (hv : v.length<2^24) :
    (splitLeaf k s key v).memD<2^65 := by
  have hp := commonPrefix_key_bound k key hkey
  have hl : (k.drop (commonPrefix k key).length).length≤k.length := by simp only [List.length_drop]; omega
  have hr : (key.drop (commonPrefix k key).length).length≤key.length := by simp only [List.length_drop]; omega
  unfold splitLeaf
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
    simp only [h1,h2] <;> cases p <;>
    simp_all [wrapExt,newLeaf,PTrie.memD,PTrie.mem?,leafMem,valueMem,extOwnMem,
      Render.NodeInfo.hexPrefix_len] <;> omega

theorem splitExt_memory_bound (k key : List Nat) (c : PTrie) (m : Nat) (v : Bytes)
    (hkey : key.length≤2) (hk : k.length<2^34) (hm : m<2^64) (hv : v.length<2^24) :
    (splitExt k c m key v).memD<2^65 := by
  have hp := commonPrefix_key_bound k key hkey
  have hl : (k.drop (commonPrefix k key).length).length≤k.length := by simp only [List.length_drop]; omega
  have hr : (key.drop (commonPrefix k key).length).length≤key.length := by simp only [List.length_drop]; omega
  unfold splitExt
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => simp [h1,PTrie.memD,PTrie.mem?]; omega
  | cons x xs =>
    cases h2 : key.drop p.length <;>
      simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
      simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp_all [wrapExt,newLeaf,PTrie.memD,PTrie.mem?,leafMem,valueMem,extOwnMem,
        Render.NodeInfo.hexPrefix_len] <;> omega
theorem leafSplitRun_memory_bound (k key : List Nat) (s : Slot) (m : Nat) (v : Bytes)
    (hkey : key.length≤2) (hk : k.length<2^34) (hs : s.len<2^32) (hv : v.length<2^24) :
    ∀ part∈(leafSplitRun k s m key v).parts, part.output.memD<2^65 := by
  have hp := commonPrefix_key_bound k key hkey
  have hl : (k.drop (commonPrefix k key).length).length≤k.length := by simp only [List.length_drop]; omega
  have hr : (key.drop (commonPrefix k key).length).length≤key.length := by simp only [List.length_drop]; omega
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
    simp only [h1,h2] <;> cases p <;>
    simp_all [wrapRun,terminalRun,pushPart,wrapExt,newLeaf,PTrie.memD,PTrie.mem?,leafMem,valueMem,extOwnMem,
      Render.NodeInfo.hexPrefix_len] <;> (repeat' (apply And.intro)) <;> omega

theorem extSplitRun_memory_bound (k key : List Nat) (c : PTrie) (m : Nat) (v : Bytes)
    (hkey : key.length≤2) (hk : k.length<2^34) (hm : m<2^64) (hv : v.length<2^24) :
    ∀ part∈(extSplitRun k c m key v).parts, part.output.memD<2^65 := by
  have hp := commonPrefix_key_bound k key hkey
  have hl : (k.drop (commonPrefix k key).length).length≤k.length := by simp only [List.length_drop]; omega
  have hr : (key.drop (commonPrefix k key).length).length≤key.length := by simp only [List.length_drop]; omega
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => simp [h1,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;>
      simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
      simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp_all [wrapRun,terminalRun,pushPart,wrapExt,newLeaf,PTrie.memD,PTrie.mem?,leafMem,valueMem,extOwnMem,
        Render.NodeInfo.hexPrefix_len] <;> (repeat' (apply And.intro)) <;> omega
end ZkFormal.NearV3.Render.UpsGen
