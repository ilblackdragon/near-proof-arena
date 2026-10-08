import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteOccurrences

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec Assembly

private theorem slot_count {a b : Slot} (h : WriteSlotPair a b) :
    (NearSpecV3.slotVal a).length=(NearSpecV3.slotVal b).length := by cases h <;> rfl

private theorem optional_count {a b : Option Slot} (h : Option.Rel WriteSlotPair a b) :
    (NearSpecV3.optSlotVal a).length=(NearSpecV3.optSlotVal b).length := by
  cases h with
  | none=>rfl
  | some h=>exact slot_count h

mutual
theorem write_value_count : ∀{a b : PTrie},WriteTreePair a b→
    (NearSpecV3.valsOf a).length=(NearSpecV3.valsOf b).length
  | _,_,.hash _=>rfl
  | _,_,.leaf k m h=>by cases h <;> rfl
  | _,_,.ext k m h=>by
      simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals] using write_value_count h
  | _,_,.branch m h hs=>by
      simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals,kidValues,List.length_append]
        using (show (NearSpecV3.optSlotVal _).length+(kidValues _).length=(NearSpecV3.optSlotVal _).length+(kidValues _).length by rw [optional_count h,write_kid_value_count hs])
theorem write_kid_value_count : ∀{a b : Kids},WriteKidsPair a b→
    (kidValues a).length=(kidValues b).length
  | _,_,.nil=>rfl
  | _,_,.none h=>by simpa only [kidValues,NearSpecV3.kOccs] using write_kid_value_count h
  | _,_,.some h hs=>by
      simpa [kidValues,NearSpecV3.kOccs,List.flatMap_append,List.length_append,NearSpecV3.valsOf]
        using (show (NearSpecV3.valsOf _).length+(kidValues _).length=(NearSpecV3.valsOf _).length+(kidValues _).length by rw [write_value_count h,write_kid_value_count hs])
end

private theorem slot_index {a b : Slot} (h : WriteSlotPair a b) :
    slotValueIndex a=slotValueIndex b := by cases h <;> rfl

private theorem optional_index {a b : Option Slot} (h : Option.Rel WriteSlotPair a b) :
    optSlotValueIndex a=optSlotValueIndex b := by
  cases h with
  | none=>rfl
  | some h=>exact slot_index h

mutual
/-- Same-shape writes preserve every compact value ordinal, including absent
and hash-only paths, without identifying bytes by hash. -/
theorem write_value_index : ∀{a b : PTrie},WriteTreePair a b→∀key,valueIndex a key=valueIndex b key
  | _,_,.hash _,_=>rfl
  | _,_,.leaf k m h,key=>by simp only [valueIndex,slot_index h]
  | _,_,.ext k m h,key=>by simp only [valueIndex,write_value_index h]
  | _,_,.branch m h hs,[]=>optional_index h
  | _,_,.branch m h hs,n::key=>by
      simp only [valueIndex,optional_count h,write_kid_value_index hs]
theorem write_kid_value_index : ∀{a b : Kids},WriteKidsPair a b→∀n key,kidValueIndex a n key=kidValueIndex b n key
  | _,_,.nil,_,_=>rfl
  | _,_,.none _,0,_=>rfl
  | _,_,.none h,n+1,key=>write_kid_value_index h n key
  | _,_,.some h _,0,key=>write_value_index h key
  | _,_,.some h hs,n+1,key=>by
      simp only [kidValueIndex,write_value_count h,write_kid_value_index hs]
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
