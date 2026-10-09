import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupValueProvider
import ZkFormal.NearV3.Assembly.SchedulerUpsertCost
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Rcpt.Candidates.NodePostUpdate

/-- The value ID is the actual prestate forest index, with canonical zero for absence. -/
def priorValueId (before : List PTrie) (tree : PTrie) : Nat :=
  match valueIndex tree keyBwState with
  | none=>0
  | some i=>forestLookupVid before+i

private theorem append_value {α : Type} (pre middle post : List α) (i : Nat) (b : α)
    (h : middle[i]?=some b) : (pre++middle++post)[pre.length+i]?=some b := by
  have hi:=(List.getElem?_eq_some_iff.mp h).1
  simp only [List.getElem?_append,List.length_append]
  simp only [show pre.length+i<pre.length+middle.length by omega,ite_true,
    show ¬pre.length+i<pre.length by omega,ite_false,Nat.add_sub_cancel_left,h]

theorem present (before after : List PTrie) (tree : PTrie) (bytes : Bytes)
    (hr:readKey tree keyBwState "bandwidth scheduler state"=.ok (some bytes)) :
    (forestStoreViews (before++tree::after)).values[priorValueId before tree]?=
      some (seedValue (priorValueId before tree) bytes) := by
  have hf:tree.find keyBwState=some (some bytes) := by
    unfold readKey at hr
    split at hr <;> simp_all
  obtain ⟨i,hi,hb⟩:=valueIndex_complete tree keyBwState bytes hf
  rw [native_valsOf_eq] at hb
  have hg:(forestBytes (before++tree::after))[forestLookupVid before+i]?=some bytes := by
    simpa only [forestLookupVid,forestBytes,List.flatMap_append,List.flatMap_cons,List.append_assoc] using
      append_value (forestBytes before) (valsOf tree) (forestBytes after) i bytes hb
  simpa only [priorValueId,hi,forestStoreViews,Nat.zero_add] using seedValuesFrom_get 0 _ _ bytes hg

theorem absent (before : List PTrie) (tree : PTrie)
    (hr:readKey tree keyBwState "bandwidth scheduler state"=.ok none) :
    priorValueId before tree=0 := by
  have hf:tree.find keyBwState=some none := by
    unfold readKey at hr
    split at hr <;> simp_all
  cases he:valueIndex tree keyBwState with
  | none=>simp [priorValueId,he]
  | some i=>
    obtain ⟨b,hb⟩:=valueIndex_defined tree keyBwState i he
    rw [hf] at hb
    cases hb

theorem present_walk (before : List PTrie) (tree : PTrie) (bytes : Bytes)
    (hr:readKey tree keyBwState "bandwidth scheduler state"=.ok (some bytes))
    (wid : Nat) (ss : List WStep3)
    (hs:nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree keyBwState=some ss) :
    (nativeLookupWalk wid before.length (forestLookupNid before) tree ss).steps.getLast?.map lookupFinal=
      some (some (priorValueId before tree)) := by
  have hf:tree.find keyBwState=some (some bytes) := by
    unfold readKey at hr
    split at hr <;> simp_all
  obtain ⟨i,hi,_⟩:=valueIndex_complete tree keyBwState bytes hf
  rw [nativeLookupWalk_valueIndex _ _ _ _ _ _ _ hs,hi]
  simp [priorValueId,hi]
end ZkFormal.NearV3.Assembly.CodecDigest
