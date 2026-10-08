import ZkFormal.NearV3.Rcpt.Candidates.NativeNodePayload

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

theorem ValuePayloads.left {u : Inputs} {v : Nat} {as bs cs ds : List Bytes}
    (h : ValuePayloads u v (as++cs) (bs++ds)) : ValuePayloads u v as bs := by
  intro i a b ha hb
  have hla : i<as.length := (List.getElem?_eq_some_iff.mp ha).1
  have hlb : i<bs.length := (List.getElem?_eq_some_iff.mp hb).1
  exact h i a b (by simpa only [List.getElem?_append,hla,↓reduceIte] using ha)
    (by simpa only [List.getElem?_append,hlb,↓reduceIte] using hb)

theorem ValuePayloads.right {u : Inputs} {v : Nat} {as bs cs ds : List Bytes}
    (h : ValuePayloads u v (as++cs) (bs++ds)) (hl : as.length=bs.length) :
    ValuePayloads u (v+as.length) cs ds := by
  intro i a b ha hb
  have hh:=h (as.length+i) a b (by simp [List.getElem?_append,ha])
    (by simp [List.getElem?_append,hl,hb])
  simpa only [Nat.add_assoc] using hh

theorem write_opt_count {a b : Option Slot} (h : Option.Rel WriteSlotPair a b) :
    (optSlotVal a).length=(optSlotVal b).length := by
  cases h with
  | none=>rfl
  | some h=>cases h <;> rfl

theorem write_vals_count {a b : PTrie} (h : WriteTreePair a b) :
    (valsOf a).length=(valsOf b).length := by
  simpa only [Assembly.native_valsOf_eq] using write_value_count h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
