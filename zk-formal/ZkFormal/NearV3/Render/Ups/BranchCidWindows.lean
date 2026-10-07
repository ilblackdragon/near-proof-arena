import ZkFormal.NearV3.Render.Ups.SourceCidWindows

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

def kidCid : NKid→Nat
  | .node cid .. => cid
  | _ => 0

def branchCidBytes (kids : List NKid) : List Nat :=
  kids.flatMap (fun k=>if k=.none then [] else List.replicate 32 (kidCid k))

theorem kidWin_cid (kid : NKid) (w : Nat) (lastw : Bool) (slot : Option Nat) :
    (NodeGen3.kidWin kid w lastw slot).cid=kidCid kid := by cases kid <;> rfl

/-- Window numbering and slot tags do not change the serialized child-ID column. -/
theorem branchWins_cids (kids : List NKid) (hp : Nat) :
    (NodeGen3.branchWins kids).flatMap (fun f=>List.replicate (f.len hp) (fieldCid f))=
      branchCidBytes kids := by
  unfold NodeGen3.branchWins
  generalize hP : (kids.zip (List.range kids.length)).filter (fun x=>x.1≠.none)=P
  rw [List.flatMap_map]
  have h1 : ∀ (Q : List (NKid×Nat)) (L : List Nat), Q.length≤L.length →
      (Q.zip L).flatMap (fun x=>List.replicate (F.len hp (.ch (NodeGen3.kidWin x.1.1 x.2
        (x.2+1=P.length) (some x.1.2)))) (fieldCid (.ch (NodeGen3.kidWin x.1.1 x.2
        (x.2+1=P.length) (some x.1.2))))) = Q.flatMap (fun x=>List.replicate 32 (kidCid x.1)) := by
    intro Q
    induction Q with
    | nil => intro L _; rfl
    | cons q Q ih =>
      intro L hl
      cases L with
      | nil => simp at hl
      | cons l L =>
        simp only [List.zip_cons_cons,List.flatMap_cons,F.len,fieldCid,F.chw,kidWin_cid]
        simpa only [F.len,fieldCid,F.chw,kidWin_cid] using
          congrArg (fun xs : List Nat => List.replicate 32 (kidCid q.1) ++ xs) (ih L (by simpa using hl))
  rw [h1 P _ (by simp),←hP]
  have h2 : ∀ (Q : List NKid) (L : List Nat), Q.length≤L.length →
      ((Q.zip L).filter (fun x=>x.1≠.none)).flatMap (fun x=>List.replicate 32 (kidCid x.1))=
        branchCidBytes Q := by
    intro Q
    induction Q with
    | nil => intro L _; rfl
    | cons q Q ih =>
      intro L hl
      cases L with
      | nil => simp at hl
      | cons l L =>
        have ht := ih L (by simpa using hl)
        change _ = (if q=.none then [] else List.replicate 32 (kidCid q)) ++ branchCidBytes Q
        by_cases hq : q=.none
        · simpa only [List.zip_cons_cons,List.filter_cons,hq,ne_eq,not_true_eq_false,
            decide_false,Bool.false_eq_true,ite_false,ite_true,List.nil_append] using ht
        · simpa only [List.zip_cons_cons,List.filter_cons,hq,ne_eq,not_false_eq_true,
            decide_true,ite_true,ite_false,List.flatMap_cons] using
            congrArg (fun xs : List Nat => List.replicate 32 (kidCid q) ++ xs) ht
  exact h2 kids _ (by simp)

/-- A branch's child-ID bytes follow its tag/value/bitmap fields in bitmap order. -/
theorem sourceCidBytes_branch (value : Option NSlot3) (kids : List NKid) (mem : List Nat) :
    sourceCidBytes (.branch value kids mem)=
      List.replicate (if value.isSome then 39 else 3) 0 ++ branchCidBytes kids ++ List.replicate 8 0 := by
  change (NodeGen.layout (NodeGen3.fieldsOf (.branch value kids mem))
    (NodeGen3.hplenOf (.branch value kids mem))).map (fun fi=>fieldCid fi.1)=_
  rw [cidLayout_fields]
  cases value <;>
    simp only [NodeGen3.fieldsOf,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      branchWins_cids,List.append_nil]
  all_goals simp only [F.len,fieldCid,F.chw,Option.isSome,ite_true,ite_false,
    ←List.append_assoc,List.replicate_append_replicate]
  all_goals rfl

/-- The first present child's serialized window carries its occurrence ID. -/
theorem sourceCidBytes_branch_first (value : Option NSlot3) (kids : List NKid)
    (mem : List Nat) (cid clen cres : Nat) (pre post : List Nat) (i : Nat) (hi : i<32) :
    (sourceCidBytes (.branch value (.node cid clen cres pre post :: kids) mem)).getD
      ((if value.isSome then 39 else 3)+i) 0=cid := by
  rw [sourceCidBytes_branch]
  simp only [branchCidBytes,List.flatMap_cons,kidCid,reduceCtorEq,ite_false]
  rw [List.append_assoc]
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_replicate,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp only [List.getElem?_replicate_of_lt hi,Option.getD_some]
end ZkFormal.NearV3.Render.UpsGen
