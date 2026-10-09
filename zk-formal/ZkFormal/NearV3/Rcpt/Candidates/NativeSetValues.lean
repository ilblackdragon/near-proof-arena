import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteValueIndex

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec Assembly

private theorem kidValues_some (c : PTrie) (cs : Kids) :
    kidValues (.some c cs)=NearSpecV3.valsOf c++kidValues cs := by
  simp [kidValues,NearSpecV3.kOccs,List.flatMap_append,NearSpecV3.valsOf]

mutual
/-- A successful native set replaces exactly one compact value occurrence. -/
theorem native_set_values : ∀(t : PTrie)(key : List Nat)(value : Bytes)(post : PTrie),
    t.set key value=some post → ∃i,valueIndex t key=some i ∧
      NearSpecV3.valsOf post=(NearSpecV3.valsOf t).set i value ∧ i<(NearSpecV3.valsOf t).length
  | .hash _,_,_,_,h=>by simp [PTrie.set] at h
  | .leaf k s m,key,value,post,h=>by
    simp only [PTrie.set] at h
    split at h
    · rename_i he
      cases s with
      | ref n hh=>simp [Slot.get] at h
      | val b=>
        simp only [Slot.get,Option.map_some,Option.some.injEq] at h
        subst post
        exact ⟨0,by simp [valueIndex,he,slotValueIndex],rfl,by simp [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals,NearSpecV3.slotVal]⟩
    · simp at h
  | .ext k c m,key,value,post,h=>by
    simp only [PTrie.set] at h
    split at h
    · rename_i he
      cases hs:c.set (key.drop k.length) value with
      | none=>simp [hs] at h
      | some child=>
        simp only [hs,Option.map_some,Option.some.injEq] at h
        subst post
        obtain ⟨i,hi,hv,hl⟩:=native_set_values c _ value child hs
        exact ⟨i,by simp [valueIndex,he,hi],by simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals] using hv,
          by simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals] using hl⟩
    · simp at h
  | .branch v cs m,[],value,post,h=>by
    simp only [PTrie.set] at h
    split at h <;> simp at h
    subst post
    rename_i old
    exact ⟨0,rfl,rfl,by simp [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals,NearSpecV3.optSlotVal,NearSpecV3.slotVal]⟩
  | .branch v cs m,n::key,value,post,h=>by
    simp only [PTrie.set] at h
    cases hs:Kids.set cs n key value with
    | none=>simp [hs] at h
    | some children=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      obtain ⟨i,hi,hv,hl⟩:=native_kids_set_values cs n key value children hs
      refine ⟨(NearSpecV3.optSlotVal v).length+i,by simp [valueIndex,hi],?_,?_⟩
      · simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals,kidValues,List.set_append_right,hv] using
          (show NearSpecV3.optSlotVal v++kidValues children=
            (NearSpecV3.optSlotVal v++kidValues cs).set ((NearSpecV3.optSlotVal v).length+i) value by
            rw [List.set_append_right _ _ (by omega)];simp [hv])
      · simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals,kidValues] using Nat.add_lt_add_left hl (NearSpecV3.optSlotVal v).length
theorem native_kids_set_values : ∀(cs : Kids)(n : Nat)(key : List Nat)(value : Bytes)(post : Kids),
    Kids.set cs n key value=some post → ∃i,kidValueIndex cs n key=some i ∧
      kidValues post=(kidValues cs).set i value ∧ i<(kidValues cs).length
  | .nil,_,_,_,_,h=>by simp [Kids.set] at h
  | .none _,0,_,_,_,h=>by simp [Kids.set] at h
  | .some c rest,0,key,value,post,h=>by
    simp only [Kids.set] at h
    cases hs:c.set key value with
    | none=>simp [hs] at h
    | some child=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      obtain ⟨i,hi,hv,hl⟩:=native_set_values c key value child hs
      refine ⟨i,hi,?_,?_⟩
      · simp only [kidValues_some]
        change NearSpecV3.valsOf child++kidValues rest=(NearSpecV3.valsOf c++kidValues rest).set i value
        rw [List.set_append_left _ _ hl,hv]
      · simp only [kidValues_some]
        change i<(NearSpecV3.valsOf c++kidValues rest).length
        simp only [List.length_append];omega
  | .none rest,n+1,key,value,post,h=>by
    simp only [Kids.set] at h
    cases hs:Kids.set rest n key value with
    | none=>simp [hs] at h
    | some children=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      simpa [kidValueIndex,kidValues,NearSpecV3.kOccs] using native_kids_set_values rest n key value children hs
  | .some c rest,n+1,key,value,post,h=>by
    simp only [Kids.set] at h
    cases hs:Kids.set rest n key value with
    | none=>simp [hs] at h
    | some children=>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst post
      obtain ⟨i,hi,hv,hl⟩:=native_kids_set_values rest n key value children hs
      refine ⟨(NearSpecV3.valsOf c).length+i,by simp [kidValueIndex,hi],?_,?_⟩
      · simp only [kidValues_some]
        change NearSpecV3.valsOf c++kidValues children=
          (NearSpecV3.valsOf c++kidValues rest).set ((NearSpecV3.valsOf c).length+i) value
        rw [List.set_append_right _ _ (by omega)];simp [hv]
      · simp only [kidValues_some]
        change (NearSpecV3.valsOf c).length+i<(NearSpecV3.valsOf c++kidValues rest).length
        simp only [List.length_append];omega
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
