import ZkFormal.NearV3.Render.Ups.TreeViewSeeds
import ZkFormal.NearV3.Render.Ups.TreeViewBytes
import ZkFormal.NearV3.Render.Ups.NativePathNode

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

/-- Preorder node offset of a selected child, counting all preceding siblings.
It depends on occurrence position, not structural equality of subtrees. -/
def seedChildId : Nat → Kids → Nat → Nat
  | n,.nil,_ => n
  | n,.none _,0 => n
  | n,.some _ _,0 => n
  | n,.none rest,i+1 => seedChildId n rest i
  | n,.some child rest,i+1 => seedChildId (n+tsize child) rest i

theorem viewKids_selected : ∀ n kids i child,
    nativeChildAt kids i=some child →
    (viewKids n kids)[i]?=some (viewKid (seedChildId n kids i) child)
  | _,.nil,_,_,h => by simp [nativeChildAt] at h
  | _,.none _,0,_,h => by simp [nativeChildAt] at h
  | n,.some c _,0,child,h => by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child; rfl
  | n,.none rest,i+1,child,h => viewKids_selected n rest i child h
  | n,.some c rest,i+1,child,h => viewKids_selected (n+tsize c) rest i child h

theorem seed_leaf_key (tau depth n vid i : Nat) (key : List Nat) (slot : Slot) (mem : Nat)
    (hi : i<key.length) :
    [n,i,key.getD i 0,n,i+1,EK_KEY]∈edgesOf3 n (seedNodeView tau depth n vid (.leaf key slot mem)) :=
  leaf_key_edge n i _ key _ _ rfl hi

theorem seed_leaf_end (tau depth n vid : Nat) (key : List Nat) (slot : Slot) (mem : Nat) :
    [n,key.length,SYM_END,n,key.length,EK_LEND]∈edgesOf3 n
      (seedNodeView tau depth n vid (.leaf key slot mem)) :=
  leaf_end_edge n _ key _ _ rfl

theorem seed_leaf_value (tau depth n vid : Nat) (key : List Nat) (value : Bytes) (mem : Nat) :
    [n,key.length,SYM_END,vid,0,EK_VAL]∈edgesOf3 n
      (seedNodeView tau depth n vid (.leaf key (.val value) mem)) :=
  leaf_value_edge n _ key _ _ _ _ vid value.length false rfl

theorem seed_ext_key (tau depth n vid i : Nat) (key : List Nat) (child : PTrie) (mem : Nat)
    (hi : i<key.length) :
    [n,i,key.getD i 0,(extKeyTarget n i key (viewKid (n+1) child)).1,
      (extKeyTarget n i key (viewKid (n+1) child)).2,EK_KEY]∈edgesOf3 n
      (seedNodeView tau depth n vid (.ext key child mem)) :=
  ext_key_edge n i _ key _ _ rfl hi

theorem seed_branch_value (tau depth n vid : Nat) (value : Bytes) (kids : Kids) (mem : Nat) :
    [n,0,SYM_END,vid,0,EK_VAL]∈edgesOf3 n
      (seedNodeView tau depth n vid (.branch (some (.val value)) kids mem)) :=
  branch_value_edge n _ _ _ _ _ vid value.length false _ rfl

/-- Actual selected-child provider; off-path children need no abstract ID-map agreement. -/
theorem seed_branch_child (tau depth n vid slot : Nat) (value : Option Slot) (kids : Kids)
    (mem : Nat) (child : PTrie) (hc : nativeChildAt kids slot=some child)
    (hn : isNode child=true) :
    [n,0,slot,viewTarget (seedChildId (n+1) kids slot) child,0,EK_DOWN]∈edgesOf3 n
      (seedNodeView tau depth n vid (.branch value kids mem)) := by
  have hh := viewKids_selected (n+1) kids slot child hc
  simp only [viewKid,hn,ite_true] at hh
  exact branch_child_edge n slot _ _ _ _ _ _ _ _ _ rfl hh

theorem seed_branch_bitmap (tau depth n vid : Nat) (value : Option Slot) (kids : Kids) (mem : Nat) :
    (seedNodeView tau depth n vid (.branch value kids mem)).v.bmap=
      some (kidBitmap (treeKids kids),if value.isSome then 1 else 0) := by
  simp only [seedNodeView,viewNode,NodeV3.bmap]
  rw [viewKids_bitmap,treeKids_bitmap]
  cases value <;> rfl

end ZkFormal.NearV3.Render.UpsGen
