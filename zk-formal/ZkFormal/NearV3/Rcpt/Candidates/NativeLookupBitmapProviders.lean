import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupNoBitmap
import ZkFormal.NearV3.Rcpt.Candidates.NativeProviderCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

def bitmapKeysAt (n : Nat) (s : NodeS3) : List Msg :=
  (s.v.bmap.map (fun (bm,hv)=>[n,bm,hv])).toList

def indexedNodeBitmaps : Nat→List NodeS3→List Msg
  | _,[]=>[]
  | n,s::ss=>bitmapKeysAt n s++indexedNodeBitmaps (n+1) ss

theorem indexedNodeBitmaps_append (n : Nat) (a b : List NodeS3) :
    indexedNodeBitmaps n (a++b)=indexedNodeBitmaps n a++indexedNodeBitmaps (n+a.length) b := by
  induction a generalizing n with
  | nil=>simp [indexedNodeBitmaps]
  | cons s a ih=>simp [indexedNodeBitmaps,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem indexedNodeBitmaps_zip (n : Nat) (ss : List NodeS3) :
    indexedNodeBitmaps n ss=(ss.zip (List.range' n ss.length)).filterMap
      (fun (s,i)=>s.v.bmap.map (fun (bm,hv)=>[i,bm,hv])) := by
  induction ss generalizing n with
  | nil=>rfl
  | cons s ss ih=>
    simp only [indexedNodeBitmaps,List.length_cons,List.range'_succ,List.zip_cons_cons,
      List.filterMap_cons,ih,bitmapKeysAt]
    cases s.v.bmap <;> rfl

theorem indexedNodeBitmaps_zero (ss : List NodeS3) : indexedNodeBitmaps 0 ss=nodeBitmapKeys ss := by
  rw [indexedNodeBitmaps_zip]
  simp only [nodeBitmapKeys,List.range_eq_range']

theorem branch_bitmap_provider (tau depth nid vid : Nat) (value : Option Slot) (kids : Kids) (mem : Nat) :
    [nid,kidsBitmap kids 0,if value.isSome then 1 else 0]∈
      bitmapKeysAt nid (seedNodeView tau depth nid vid (.branch value kids mem)) := by
  rw [bitmapKeysAt,seed_branch_bitmap,treeKids_bitmap]
  simp

theorem indexed_child_bitmaps (tau depth nid vid : Nat) : ∀kids j child,
    nativeChildAt kids j=some child→
    ∀e∈indexedNodeBitmaps (seedChildId nid kids j)
      (seedNodesT tau depth (seedChildId nid kids j) (lookupChildVid vid kids j) child),
      e∈indexedNodeBitmaps nid (seedKidsT tau depth nid vid kids)
  | .nil,_,_,h=>by simp [nativeChildAt] at h
  | .none _,0,_,h=>by simp [nativeChildAt] at h
  | .some c rest,0,child,h=>by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child
    intro e he
    rw [seedKidsT,indexedNodeBitmaps_append]
    exact List.mem_append_left _ he
  | .none rest,j+1,child,h=>indexed_child_bitmaps tau depth nid vid rest j child h
  | .some c rest,j+1,child,h=>by
    intro e he
    have hh:=indexed_child_bitmaps tau depth (nid+tsize c) (vid+(valsOf c).length) rest j child h e he
    rw [seedKidsT,indexedNodeBitmaps_append,seedNodesT_length]
    exact List.mem_append_right _ hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
