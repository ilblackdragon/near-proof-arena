import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupValueIndex

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem nativeLookupWalk_valueIndex (wid tau nid vid : Nat) (tree : PTrie) (key : List Nat)
    (ss : List WStep3) (h : nativeLookupSteps nid vid tree key=some ss) :
    (nativeLookupWalk wid tau nid tree ss).steps.getLast?.map lookupFinal=
      some ((valueIndex tree key).map (vid+·)) := by
  change ([lookupEdge 0 SYM_START [0,tau,SYM_START,viewTarget nid tree,0,EK_DOWN]]++ss).getLast?.map lookupFinal=_
  rw [lookup_append_final _ ss (native_lookup_nonempty _ _ _ _ _ h)]
  exact nativeLookup_valueIndex nid vid tree key ss h

private theorem append_value {α : Type} (pre middle post : List α) (i : Nat) (b : α)
    (h : middle[i]?=some b) : (pre++middle++post)[pre.length+i]?=some b := by
  have hi:= (List.getElem?_eq_some_iff.mp h).1
  simp only [List.getElem?_append,List.length_append]
  simp only [show pre.length+i<pre.length+middle.length by omega,ite_true,
    show ¬pre.length+i<pre.length by omega,ite_false,Nat.add_sub_cancel_left,h]

/-- A present lookup terminates at the SAME globally allocated value record,
whose native bytes equal the actual native read result. -/
theorem native_forest_value_provider (before after : List PTrie) (tree : PTrie)
    (wid : Nat) (key : List Nat) (ss : List WStep3) (b : Bytes)
    (h : nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree key=some ss)
    (hf : tree.find key=some (some b)) :
    ∃vid,(nativeLookupWalk wid before.length (forestLookupNid before) tree ss).steps.getLast?.map lookupFinal=some (some vid) ∧
      (forestStoreViews (before++tree::after)).values[vid]?=some (seedValue vid b) := by
  obtain ⟨i,hi,hb⟩:=valueIndex_complete tree key b hf
  rw [native_valsOf_eq] at hb
  refine ⟨forestLookupVid before+i,?_,?_⟩
  · rw [nativeLookupWalk_valueIndex _ _ _ _ _ _ _ h,hi]
    rfl
  · have hg : (forestBytes (before++tree::after))[forestLookupVid before+i]?=some b := by
      simpa only [forestLookupVid,forestBytes,List.flatMap_append,List.flatMap_cons,List.append_assoc] using
        append_value (forestBytes before) (valsOf tree) (forestBytes after) i b hb
    simpa only [forestStoreViews,Nat.zero_add] using seedValuesFrom_get 0 _ _ b hg

/-- Proven absence has no terminal value provider. -/
theorem native_lookup_absent_final (nid vid wid tau : Nat) (tree : PTrie) (key : List Nat)
    (ss : List WStep3) (h : nativeLookupSteps nid vid tree key=some ss)
    (hf : tree.find key=some none) :
    (nativeLookupWalk wid tau nid tree ss).steps.getLast?.map lookupFinal=some none := by
  have hv : valueIndex tree key=none := by
    cases he : valueIndex tree key with
    | none=>rfl
    | some i=>
      obtain ⟨b,hb⟩:=valueIndex_defined tree key i he
      rw [hf] at hb
      cases hb
  rw [nativeLookupWalk_valueIndex _ _ _ _ _ _ _ h,hv]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
