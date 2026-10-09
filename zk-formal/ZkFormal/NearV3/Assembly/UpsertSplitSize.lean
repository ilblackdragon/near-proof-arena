import ZkFormal.NearV3.Assembly.UpsertAncestorCost
import ZkFormal.NearV3.Assembly.UpsertSourceCost

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

def outputByteCharge (run : TreeRun) : Nat :=
  (run.parts.map (fun p => (nodeEnc p.output).length)).sum

@[simp] theorem outputByteCharge_push (run : TreeRun) (p : TreePart) :
    outputByteCharge (pushPart run p)=outputByteCharge run+(nodeEnc p.output).length := by
  simp [outputByteCharge,pushPart]

theorem hashes_kidsFrom_bound : ∀ n i f,
    (∀ j c,f j=some c → c.hashOf.length≤32) →
    (Kids.hashes (kidsFrom n i f)).length≤32*n
  | 0,_,_,_ => by simp [kidsFrom,Kids.hashes]
  | n+1,i,f,hf => by
    have ih := hashes_kidsFrom_bound n (i+1) f hf
    cases h : f i with
    | none => simp [kidsFrom,h,Kids.hashes]; omega
    | some c =>
      have hc := hf i c h
      simp [kidsFrom,h,Kids.hashes]; omega

theorem hashes_kids1_bound (x : Nat) (c : PTrie) (hc : c.hashOf.length≤32) :
    (Kids.hashes (kids1 x c)).length≤512 := by
  apply hashes_kidsFrom_bound
  intro j child hj
  split at hj
  · cases hj; exact hc
  · contradiction

theorem hashes_kids2_bound (x y : Nat) (c d : PTrie)
    (hc : c.hashOf.length≤32) (hd : d.hashOf.length≤32) :
    (Kids.hashes (kids2 x c y d)).length≤512 := by
  apply hashes_kidsFrom_bound
  intro j child hj
  split at hj
  · cases hj; exact hc
  · split at hj
    · cases hj; exact hd
    · contradiction

theorem node_hash_width {t : PTrie} (hn : isNode t=true) : t.hashOf.length=32 := by
  rw [hashOf_eq_enc _ hn]; simp

theorem split_branch_size (sv : Option Slot) (cs : Kids) (mem : Nat)
    (hv : ∀ s,sv=some s → s.valueRef.length≤36) (hc : (Kids.hashes cs).length≤512) :
    (nodeEnc (.branch sv cs mem)).length≤559 := by
  cases sv with
  | none => simp [nodeEnc]; omega
  | some s => have hs := hv s rfl; simp [nodeEnc]; omega

/-- Wide enough for every sparse split branch, without assuming distinct or
in-range child selectors. Exact slot bounds are unnecessary for this cost. -/
theorem split_one_size (sv : Option Slot) (x : Nat) (c : PTrie) (mem : Nat)
    (hv : ∀ s,sv=some s → s.valueRef.length≤36) (hc : c.hashOf.length≤32) :
    (nodeEnc (.branch sv (kids1 x c) mem)).length≤559 :=
  split_branch_size sv _ mem hv (hashes_kids1_bound x c hc)

theorem split_two_size (sv : Option Slot) (x y : Nat) (c d : PTrie) (mem : Nat)
    (hv : ∀ s,sv=some s → s.valueRef.length≤36)
    (hc : c.hashOf.length≤32) (hd : d.hashOf.length≤32) :
    (nodeEnc (.branch sv (kids2 x c y d) mem)).length≤559 :=
  split_branch_size sv _ mem hv (hashes_kids2_bound x y c d hc hd)

theorem split_one_none_size (x : Nat) (c : PTrie) (mem : Nat) (hc : c.hashOf.length≤32) :
    (nodeEnc (.branch none (kids1 x c) mem)).length≤559 :=
  split_one_size none x c mem (by simp) hc

theorem split_one_some_size (s : Slot) (x : Nat) (c : PTrie) (mem : Nat)
    (hs : s.valueRef.length≤36) (hc : c.hashOf.length≤32) :
    (nodeEnc (.branch (some s) (kids1 x c) mem)).length≤559 :=
  split_one_size (some s) x c mem (by intro t h; cases h; exact hs) hc

theorem split_two_none_size (x y : Nat) (c d : PTrie) (mem : Nat)
    (hc : c.hashOf.length≤32) (hd : d.hashOf.length≤32) :
    (nodeEnc (.branch none (kids2 x c y d) mem)).length≤559 :=
  split_two_size none x y c d mem (by simp) hc hd

theorem leafSplit_output_charge (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hs : NearSpec.slotOk s=true) (hk : key.length≤2) :
    outputByteCharge (leafSplitRun k s m key v)≤
      sourceByteCharge (leafSplitRun k s m key v)+4096 := by
  have hslen := slot_valueRef_width hs
  have hvlen : (Slot.val v).valueRef.length=36 := by simp [Slot.valueRef]
  have hl := congrArg List.length (commonPrefix_left k key)
  have hr := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hl hr
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
    simp only [h1,h2] <;> cases p <;>
    simp only [outputByteCharge,sourceByteCharge,terminalRun,wrapRun,pushPart,newLeaf,wrapExt,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.map_append,List.sum_append] <;>
    grind only [native_leaf_size,native_ext_size,split_one_none_size,split_one_some_size,split_two_none_size,node_hash_width,isNode,List.length_cons,List.length_nil]

theorem extSplit_output_charge (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hc : c.wf=true) (hk : key.length≤2) :
    outputByteCharge (extSplitRun k c m key v)≤
      sourceByteCharge (extSplitRun k c m key v)+4096 := by
  have hclen := hashOf_len_of_wf c hc
  have hvlen : (Slot.val v).valueRef.length=36 := by simp [Slot.valueRef]
  have hl := congrArg List.length (commonPrefix_left k key)
  have hr := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hl hr
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => simp [h1,outputByteCharge,sourceByteCharge,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;>
      simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
      simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp only [outputByteCharge,sourceByteCharge,terminalRun,wrapRun,pushPart,newLeaf,wrapExt,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.map_append,List.sum_append] <;>
      grind only [native_leaf_size,native_ext_size,split_one_none_size,split_one_some_size,
        split_two_none_size,node_hash_width,isNode,List.length_cons,List.length_nil]

theorem leafSplit_output_node_charge (k : List Nat) (s : Slot) (m : Nat) (key : List Nat) (v : Bytes)
    (hs : NearSpec.slotOk s=true) (hk : key.length≤2) :
    outputByteCharge (leafSplitRun k s m key v)≤
      (nodeEnc (.leaf k s m)).length+4096 := by
  have hslen := slot_valueRef_width hs
  have hvlen : (Slot.val v).valueRef.length=36 := by simp [Slot.valueRef]
  have hl := congrArg List.length (commonPrefix_left k key)
  have hr := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hl hr
  unfold leafSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
    simp only [h1,h2] <;> cases p <;>
    simp only [outputByteCharge,sourceByteCharge,terminalRun,wrapRun,pushPart,newLeaf,wrapExt,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.map_append,List.sum_append] <;>
    grind only [native_leaf_size,native_ext_size,split_one_none_size,split_one_some_size,split_two_none_size,node_hash_width,isNode,List.length_cons,List.length_nil]

theorem extSplit_output_node_charge (k : List Nat) (c : PTrie) (m : Nat) (key : List Nat) (v : Bytes)
    (hc : c.wf=true) (hk : key.length≤2) :
    outputByteCharge (extSplitRun k c m key v)≤
      (nodeEnc (.ext k c m)).length+4096 := by
  have hclen := hashOf_len_of_wf c hc
  have hvlen : (Slot.val v).valueRef.length=36 := by simp [Slot.valueRef]
  have hl := congrArg List.length (commonPrefix_left k key)
  have hr := congrArg List.length (commonPrefix_right k key)
  simp only [List.length_append] at hl hr
  unfold extSplitRun
  generalize commonPrefix k key=p at *
  cases h1 : k.drop p.length with
  | nil => simp [h1,outputByteCharge,sourceByteCharge,terminalRun]
  | cons x xs =>
    cases h2 : key.drop p.length <;>
      simp only [h1,h2,List.length_cons,List.length_nil] at hl hr <;>
      simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp only [outputByteCharge,sourceByteCharge,terminalRun,wrapRun,pushPart,newLeaf,wrapExt,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.map_append,List.sum_append] <;>
      grind only [native_leaf_size,native_ext_size,split_one_none_size,split_one_some_size,
        split_two_none_size,node_hash_width,isNode,List.length_cons,List.length_nil]

end ZkFormal.NearV3.Assembly
