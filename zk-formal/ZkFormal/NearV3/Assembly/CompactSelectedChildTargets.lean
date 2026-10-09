import ZkFormal.NearV3.Assembly.CompactBranchValueTargets

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

private theorem range_select {α : Type} (n target : Nat) (F : Nat→α) (ht : target<n) :
    (List.range n).flatMap (fun j=>if j=target then [F j] else [])=[F target] := by
  induction n generalizing target F with
  | zero=>omega
  | succ n ih=>
    cases target with
    | zero=>simp [List.range_succ_eq_map,List.flatMap_map]
    | succ target=>
      simp only [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,Nat.zero_ne_add_one,
        ite_false,List.nil_append,Nat.add_right_cancel_iff]
      simpa only [Nat.succ_eq_add_one,Nat.add_right_cancel_iff] using
        ih target (fun j=>F (j+1)) (by omega)

def targetWindow (I : Render.UpsInst) (k : Nat) : Nat :=
  if S15B I (part I k)=true then nWin (part I k).shape-1 else 0

private theorem target_iff (I : Render.UpsInst) (k j : Nat)
    (hn : 0<nWin (part I k).shape) : TgtB I (part I k) 7 j=true ↔ j=targetWindow I k := by
  cases hs:S15B I (part I k) <;> simp [TgtB,FwB,LastwB,targetWindow,hs] <;> omega

/-- RDB/RBI select exactly the first or last physical child window according
to the actual nibble traversal. Both cases target previous output job k. -/
theorem selected_child_field (I : Render.UpsInst) (k pos j : Nat)
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=0∨(part I k).kind=5)
    (hn : 0<nWin (part I k).shape) :
    fieldDigestMsgs I k pos 7 j=
      if j=targetWindow I k then [digestWindow I k pos k
        (if (part I k).kind=5 then 50 else (part I k).clen)] else [] := by
  rw [child_field_target]
  have ht:=target_iff I k j hn
  rcases hk with hk|hk
  · have hj:=hp.jmD (Or.inl hk)
    simp only [WfrB,WnB,hk,beq_self_eq_true,Bool.true_or,Bool.true_and,Bool.false_or,
      Bool.false_and,Bool.or_false,Bool.and_self]
    simp [ht,hj]
  · simp only [WfrB,WnB,hk,beq_self_eq_true,Bool.true_or,Bool.true_and,Bool.false_or,
      Bool.false_and,Bool.or_false,Bool.and_self]
    by_cases h:j=targetWindow I k
    · have hh:=ht.mpr h
      have htarget : TgtB I (part I k) 7 (targetWindow I k)=true := by simpa only [h] using hh
      simp [hh,h,htarget]
    · have hh : TgtB I (part I k) 7 j=false := Bool.eq_false_iff.mpr (fun he=>h (ht.mp he))
      simp [hh,h]

/-- All physical branch child windows contain precisely one selected digest
lookup; arbitrary unselected siblings preserve their zero multiplicity. -/
theorem selected_child_inventory (I : Render.UpsInst) (k base : Nat)
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=0∨(part I k).kind=5)
    (hn : 0<nWin (part I k).shape) :
    (List.range (nWin (part I k).shape)).flatMap
      (fun j=>fieldDigestMsgs I k (base+32*j) 7 j)=
      [digestWindow I k (base+32*targetWindow I k) k
        (if (part I k).kind=5 then 50 else (part I k).clen)] := by
  simp only [selected_child_field I k _ _ hp hk hn]
  apply range_select
  unfold targetWindow
  split <;> omega

/-- Complete RDB/RBI physical inventory, including a copied value field when
present. Child nonemptiness remains an ordinary native-shape obligation. -/
theorem selected_branch_inventory (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k))
    (hk : (part I k).kind=0∨(part I k).kind=5) (hn : 0<nWin (part I k).shape) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k ((if (part I k).ty=2 then 3 else 39)+32*targetWindow I k) k
        (if (part I k).kind=5 then 50 else (part I k).clen)] := by
  have ht:=hp.tyBr (by omega)
  have hb:=hf.ty
  rcases (show (part I k).ty=2∨(part I k).ty=3 by omega) with hty|hty
  · rw [branch_digest_inventory I k hf hty,selected_child_inventory I k 3 hp hk hn]
    simp only [hty,ite_true]
  · rw [value_branch_digest_inventory I k hf hty,value_field_target,
      selected_child_inventory I k 39 hp hk hn]
    rcases hk with hk|hk <;> simp [VcpB,hk,hty]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
