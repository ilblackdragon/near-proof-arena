import ZkFormal.NearV3.Assembly.ReadUnfoldBound

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def slotValueIndex : Slot → Option Nat
  | .val _ => some 0
  | .ref _ _ => none

def optSlotValueIndex : Option Slot → Option Nat
  | some s => slotValueIndex s
  | none => none

def kidValues (cs : Kids) : List Bytes := (NearSpecV3.kOccs cs).flatMap NearSpecV3.ownVals

/- Ordinal in the existing per-occurrence revealed-value list, not a byte hash. -/
mutual
def valueIndex : PTrie → List Nat → Option Nat
  | .hash _, _ => none
  | .leaf k s _, key => if k == key then slotValueIndex s else none
  | .ext k c _, key => if isPrefix k key then valueIndex c (key.drop k.length) else none
  | .branch v _ _, [] => optSlotValueIndex v
  | .branch v cs _, n::key => (kidValueIndex cs n key).map ((NearSpecV3.optSlotVal v).length + ·)
def kidValueIndex : Kids → Nat → List Nat → Option Nat
  | .nil, _, _ => none
  | .none _, 0, _ => none
  | .some c _, 0, key => valueIndex c key
  | .none cs, n+1, key => kidValueIndex cs n key
  | .some c cs, n+1, key => (kidValueIndex cs n key).map ((NearSpecV3.valsOf c).length + ·)
end

private theorem slot_index {s : Slot} {b : Bytes} (h : s.get.map some = some (some b)) :
    slotValueIndex s = some 0 ∧ (NearSpecV3.slotVal s)[0]? = some b := by
  cases s with
  | ref => cases h
  | val v => cases h; exact ⟨rfl,rfl⟩

mutual
theorem valueIndex_complete : ∀ t key b, t.find key = some (some b) →
    ∃ i, valueIndex t key = some i ∧ (NearSpecV3.valsOf t)[i]? = some b
  | .hash _, _, _, h => by cases h
  | .leaf k s m, key, b, h => by
    simp only [PTrie.find] at h
    split at h
    · rename_i he
      obtain ⟨hi,hb⟩ := slot_index h
      refine ⟨0,?_,?_⟩
      · simp [valueIndex,he,hi]
      · simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals] using hb
    · cases h
  | .ext k c m, key, b, h => by
    simp only [PTrie.find] at h
    split at h
    · rename_i he
      obtain ⟨i,hi,hb⟩ := valueIndex_complete c _ b h
      refine ⟨i,by simp [valueIndex,he,hi],?_⟩
      simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals] using hb
    · cases h
  | .branch v cs m, [], b, h => by
    cases v with
    | none => cases h
    | some s =>
      obtain ⟨hi,hb⟩ := slot_index h
      refine ⟨0,hi,?_⟩
      cases s with
      | ref => cases hi
      | val b' => simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals,NearSpecV3.optSlotVal,NearSpecV3.slotVal] using hb
  | .branch v cs m, n::key, b, h => by
    obtain ⟨i,hi,hb⟩ := kidValueIndex_complete cs n key b h
    refine ⟨(NearSpecV3.optSlotVal v).length+i,by simp [valueIndex,hi],?_⟩
    simpa [NearSpecV3.valsOf,NearSpecV3.occs,NearSpecV3.ownVals,kidValues] using
      (show (NearSpecV3.optSlotVal v ++ kidValues cs)[(NearSpecV3.optSlotVal v).length+i]? = some b by
        simp [List.getElem?_append,hb])
theorem kidValueIndex_complete : ∀ cs n key b, Kids.find cs n key = some (some b) →
    ∃ i, kidValueIndex cs n key = some i ∧ (kidValues cs)[i]? = some b
  | .nil, _, _, _, h => by cases h
  | .none _, 0, _, _, h => by cases h
  | .some c cs, 0, key, b, h => by
    obtain ⟨i,hi,hb⟩ := valueIndex_complete c key b h
    refine ⟨i,hi,?_⟩
    have hi' : i < (NearSpecV3.valsOf c).length := (List.getElem?_eq_some_iff.mp hb).1
    simpa [kidValues,NearSpecV3.kOccs,List.flatMap_append,NearSpecV3.valsOf] using
      (show (NearSpecV3.valsOf c ++ kidValues cs)[i]? = some b by simpa only [List.getElem?_append,hi',↓reduceIte] using hb)
  | .none cs, n+1, key, b, h => kidValueIndex_complete cs n key b h
  | .some c cs, n+1, key, b, h => by
    obtain ⟨i,hi,hb⟩ := kidValueIndex_complete cs n key b h
    refine ⟨(NearSpecV3.valsOf c).length+i,by simp [kidValueIndex,hi],?_⟩
    simpa [kidValues,NearSpecV3.kOccs,List.flatMap_append,NearSpecV3.valsOf] using
      (show (NearSpecV3.valsOf c ++ kidValues cs)[(NearSpecV3.valsOf c).length+i]? = some b by
        simp [List.getElem?_append,hb])
end

mutual
theorem valueIndex_defined : ∀ t key i, valueIndex t key = some i →
    ∃ b, t.find key = some (some b)
  | .hash _, _, _, h => by cases h
  | .leaf k s m, key, i, h => by
    simp only [valueIndex] at h
    split at h
    · rename_i he
      have heq : k = key := by simpa using he
      cases s with
      | ref => cases h
      | val b => exact ⟨b,by simp [PTrie.find,heq,Slot.get]⟩
    · cases h
  | .ext k c m, key, i, h => by
    simp only [valueIndex] at h
    split at h
    · rename_i he
      obtain ⟨b,hb⟩ := valueIndex_defined c _ i h
      exact ⟨b,by simp [PTrie.find,he,hb]⟩
    · cases h
  | .branch v cs m, [], i, h => by
    cases v with
    | none => cases h
    | some s =>
      cases s with
      | ref => cases h
      | val b => exact ⟨b,rfl⟩
  | .branch v cs m, n::key, i, h => by
    simp only [valueIndex] at h
    cases hi : kidValueIndex cs n key with
    | none => simp [hi] at h
    | some j => exact kidsValueIndex_defined cs n key j hi
theorem kidsValueIndex_defined : ∀ cs n key i, kidValueIndex cs n key = some i →
    ∃ b, Kids.find cs n key = some (some b)
  | .nil, _, _, _, h => by cases h
  | .none _, 0, _, _, h => by cases h
  | .some c cs, 0, key, i, h => valueIndex_defined c key i h
  | .none cs, n+1, key, i, h => kidsValueIndex_defined cs n key i h
  | .some c cs, n+1, key, i, h => by
    simp only [kidValueIndex] at h
    cases hi : kidValueIndex cs n key with
    | none => simp [hi] at h
    | some j => exact kidsValueIndex_defined cs n key j hi
end

theorem valueIndex_bound {t : PTrie} {key : List Nat} {i : Nat}
    (h : valueIndex t key = some i) : i < (NearSpecV3.valsOf t).length := by
  obtain ⟨b,hb⟩ := valueIndex_defined t key i h
  obtain ⟨j,hj,hget⟩ := valueIndex_complete t key b hb
  rw [h] at hj
  cases hj
  exact (List.getElem?_eq_some_iff.mp hget).1

theorem kidValueIndex_bound {cs : Kids} {n : Nat} {key : List Nat} {i : Nat}
    (h : kidValueIndex cs n key = some i) : i < (kidValues cs).length := by
  obtain ⟨b,hb⟩ := kidsValueIndex_defined cs n key i h
  obtain ⟨j,hj,hget⟩ := kidValueIndex_complete cs n key b hb
  rw [h] at hj
  cases hj
  exact (List.getElem?_eq_some_iff.mp hget).1

private theorem offset_some {o : Option Nat} {n i : Nat}
    (h : o.map (n + ·) = some i) : ∃ j, o = some j ∧ n+j=i := by
  cases o with
  | none => cases h
  | some j => exact ⟨j,rfl,by simpa using h⟩

private theorem optSlot_index_zero {v : Option Slot} {i : Nat}
    (h : optSlotValueIndex v = some i) : i=0 ∧ (NearSpecV3.optSlotVal v).length=1 := by
  cases v with
  | none => cases h
  | some s => cases s with
    | ref => cases h
    | val b => cases h; exact ⟨rfl,rfl⟩

mutual
/-- Equal occurrence value IDs force equal native keys, even if bytes repeat. -/
theorem valueIndex_key_unique : ∀ t a b i,
    valueIndex t a = some i → valueIndex t b = some i → a=b
  | .hash _, _, _, _, h, _ => by cases h
  | .leaf k s m, a, b, i, ha, hb => by
    simp only [valueIndex] at ha hb
    split at ha <;> try cases ha
    split at hb <;> try cases hb
    rename_i ea eb
    have ea' : k=a := by simpa using ea
    have eb' : k=b := by simpa using eb
    exact ea'.symm.trans eb'
  | .ext k c m, a, b, i, ha, hb => by
    simp only [valueIndex] at ha hb
    split at ha <;> try cases ha
    split at hb <;> try cases hb
    rename_i ea eb
    have he := valueIndex_key_unique c _ _ i ha hb
    obtain ⟨aa,rfl⟩ := (NearSpec.isPrefix_iff k a).mp ea
    obtain ⟨bb,rfl⟩ := (NearSpec.isPrefix_iff k b).mp eb
    simpa using congrArg (List.append k) he
  | .branch v cs m, [], [], i, _, _ => rfl
  | .branch v cs m, [], n::b, i, ha, hb => by
    obtain ⟨hi,hv⟩ := optSlot_index_zero ha
    obtain ⟨j,hj,he⟩ := offset_some hb
    omega
  | .branch v cs m, n::a, [], i, ha, hb => by
    obtain ⟨hi,hv⟩ := optSlot_index_zero hb
    obtain ⟨j,hj,he⟩ := offset_some ha
    omega
  | .branch v cs m, n::a, q::b, i, ha, hb => by
    obtain ⟨j,hj,he⟩ := offset_some ha
    obtain ⟨l,hl,hf⟩ := offset_some hb
    have hsame : j=l := by omega
    subst l
    obtain ⟨rfl,rfl⟩ := kidValueIndex_key_unique cs n q a b j hj hl
    rfl
theorem kidValueIndex_key_unique : ∀ cs n m a b i,
    kidValueIndex cs n a = some i → kidValueIndex cs m b = some i → n=m ∧ a=b
  | .nil, _, _, _, _, _, h, _ => by cases h
  | .none _, 0, _, _, _, _, h, _ => by cases h
  | .none _, _, 0, _, _, _, _, h => by cases h
  | .none cs, n+1, m+1, a, b, i, ha, hb => by
    obtain ⟨rfl,rfl⟩ := kidValueIndex_key_unique cs n m a b i ha hb
    exact ⟨rfl,rfl⟩
  | .some c cs, 0, 0, a, b, i, ha, hb =>
    ⟨rfl,valueIndex_key_unique c a b i ha hb⟩
  | .some c cs, 0, m+1, a, b, i, ha, hb => by
    have hi := valueIndex_bound ha
    obtain ⟨j,hj,he⟩ := offset_some hb
    omega
  | .some c cs, n+1, 0, a, b, i, ha, hb => by
    have hi := valueIndex_bound hb
    obtain ⟨j,hj,he⟩ := offset_some ha
    omega
  | .some c cs, n+1, m+1, a, b, i, ha, hb => by
    obtain ⟨j,hj,he⟩ := offset_some ha
    obtain ⟨l,hl,hf⟩ := offset_some hb
    have hsame : j=l := by omega
    subst l
    obtain ⟨rfl,rfl⟩ := kidValueIndex_key_unique cs n m a b j hj hl
    exact ⟨rfl,rfl⟩
end

end ZkFormal.NearV3.Assembly
