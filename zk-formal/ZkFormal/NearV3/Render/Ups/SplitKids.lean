import ZkFormal.NearV3.Render.Ups.PostSnapshot
import ZkFormal.NearV3.Render.Ups.SplitBitmap

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def oneKid (slot : Nat) (kid : NKid) : List NKid :=
  List.replicate slot .none++kid::List.replicate (15-slot) .none

def twoEdgeKids (ts x : Nat) (old new : NKid) : List NKid :=
  if ts=1 then new::List.replicate (x-1) .none++old::List.replicate (15-x) .none
  else List.replicate x .none++old::List.replicate (14-x) .none++[new]

def splitKids (I : UpsInst) (old new : NKid) : List NKid :=
  if I.ci=4 then oneKid (splitNewSlot I) new
  else if splitHasNew I then twoEdgeKids I.ts I.x old new else oneKid I.x old

theorem oneKid_length (x : Nat) (kid : NKid) (hx : x<16) : (oneKid x kid).length=16 := by
  simp [oneKid]; omega

theorem oneKid_at (x j : Nat) (kid : NKid) (hx : x<16) (hj : j<16) :
    (oneKid x kid).getD j .none=if j=x then kid else .none := by
  simp [oneKid,List.getD_eq_getElem?_getD,List.getElem?_append,List.getElem?_replicate,List.getElem?_cons]
  repeat' split
  all_goals simp_all <;> omega

theorem twoEdgeKids_length (ts x : Nat) (old new : NKid) (hx : x<16)
    (hd : x≠if ts=1 then 0 else 15) : (twoEdgeKids ts x old new).length=16 := by
  by_cases h : ts=1 <;> simp [twoEdgeKids,h] at hd ⊢ <;> omega

theorem twoEdgeKids_at (ts x j : Nat) (old new : NKid) (hx : x<16) (hj : j<16)
    (hd : x≠if ts=1 then 0 else 15) :
    (twoEdgeKids ts x old new).getD j .none=
      if j=x then old else if j=(if ts=1 then 0 else 15) then new else .none := by
  by_cases ht : ts=1
  · simp [twoEdgeKids,ht,List.getD_eq_getElem?_getD,List.getElem?_append,List.getElem?_replicate,List.getElem?_cons]
    simp [ht] at hd
    repeat' split
    all_goals simp_all <;> omega
  · simp [twoEdgeKids,ht,List.getD_eq_getElem?_getD,List.getElem?_append,List.getElem?_replicate,List.getElem?_cons]
    simp [ht] at hd
    repeat' split
    all_goals simp_all <;> omega

@[simp] theorem oneKid_bytes (x : Nat) (kid : NKid) (post : Bool) :
    (oneKid x kid).flatMap (NKid.bytes post)=kid.bytes post := by
  simp [oneKid,List.flatMap_replicate,NKid.bytes]

@[simp] theorem twoEdgeKids_bytes (ts x : Nat) (old new : NKid) (post : Bool) :
    (twoEdgeKids ts x old new).flatMap (NKid.bytes post)=
      if ts=1 then new.bytes post++old.bytes post else old.bytes post++new.bytes post := by
  by_cases h : ts=1 <;> simp [twoEdgeKids,h,List.flatMap_replicate,NKid.bytes]

end ZkFormal.NearV3.Render.UpsGen
