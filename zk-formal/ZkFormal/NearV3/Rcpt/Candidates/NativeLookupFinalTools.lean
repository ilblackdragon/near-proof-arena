import ZkFormal.NearV3.Rcpt.Candidates.NativeAccessKeyRows
import ZkFormal.NearV3.Assembly.ValueIndex

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem extensionMismatchFix_final (nid : Nat) (child : PTrie) (len : Nat) (ss : List WStep3) :
    (extensionMismatchFix nid child len ss).getLast?.map lookupFinal=ss.getLast?.map lookupFinal := by
  unfold extensionMismatchFix
  split
  · simp only [List.getLast?_map,Option.map_map,Function.comp_def,extensionMismatchStep_lookupFinal]
  · rfl

theorem lookup_append_final (pre tail : List WStep3) (hn : tail≠[]) :
    (pre++tail).getLast?.map lookupFinal=tail.getLast?.map lookupFinal := by
  rw [List.getLast?_append]
  cases hl : tail.getLast? with
  | none=>have hh:=List.getLast?_eq_none_iff.mp hl;exact False.elim (hn hh)
  | some s=>rfl

theorem native_lookup_nonempty (nid vid : Nat) (t : PTrie) (key : List Nat) (ss : List WStep3)
    (h : nativeLookupSteps nid vid t key=some ss) : ss≠[] := by
  have hl:=nativeLookupSteps_length nid vid t key ss h
  intro he
  rw [he] at hl
  simp at hl

theorem leaf_lookup_valueIndex (nid vid : Nat) (slot : Slot) (mem : Nat) (stored key : List Nat)
    (ss : List WStep3) (h : leafLookupSteps nid vid slot 0 stored key=some ss) :
    ss.getLast?.map lookupFinal=some ((valueIndex (.leaf stored slot mem) key).map (vid+·)) := by
  rw [leafLookupSteps_final nid vid slot 0 stored key ss h]
  by_cases he : stored=key
  · subst key
    have hd:=leafLookupSteps_defined nid vid slot 0 stored stored
    rw [h] at hd
    cases slot <;> simp_all [PTrie.find,Slot.get,valueIndex,slotValueIndex]
  · simp [valueIndex,he]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
