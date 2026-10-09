import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPrestate

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

mutual
/-- Updating an already revealed value requires no structural insertion. -/
theorem native_set_exists : ∀(t : PTrie)(key : List Nat)(old value : Bytes),
    t.find key=some (some old) → ∃post,t.set key value=some post
  | .hash _,_,_,_,h=>by simp [PTrie.find] at h
  | .leaf k s m,key,old,value,h=>by
    simp only [PTrie.find] at h
    split at h
    · rename_i he
      cases hs:s.get with
      | none=>simp [hs] at h
      | some b=>simp [PTrie.set,he,hs]
    · simp at h
  | .ext k c m,key,old,value,h=>by
    simp only [PTrie.find] at h
    split at h
    · rename_i he
      obtain ⟨post,hpost⟩:=native_set_exists c _ old value h
      simp [PTrie.set,he,hpost]
    · simp at h
  | .branch v cs m,[],old,value,h=>by
    cases v with
    | none=>simp [PTrie.find] at h
    | some s=>
      cases s with
      | ref n hh=>simp [PTrie.find,Slot.get] at h
      | val b=>simp [PTrie.set]
  | .branch v cs m,n::key,old,value,h=>by
    obtain ⟨post,hpost⟩:=native_kids_set_exists cs n key old value h
    simp [PTrie.set,hpost]
theorem native_kids_set_exists : ∀(cs : Kids)(n : Nat)(key : List Nat)(old value : Bytes),
    Kids.find cs n key=some (some old) → ∃post,Kids.set cs n key value=some post
  | .nil,_,_,_,_,h=>by simp [Kids.find] at h
  | .none _,0,_,_,_,h=>by simp [Kids.find] at h
  | .some c rest,0,key,old,value,h=>by
    obtain ⟨post,hpost⟩:=native_set_exists c key old value h
    simp [Kids.set,hpost]
  | .none rest,n+1,key,old,value,h=>by
    obtain ⟨post,hpost⟩:=native_kids_set_exists rest n key old value h
    simp [Kids.set,hpost]
  | .some c rest,n+1,key,old,value,h=>by
    obtain ⟨post,hpost⟩:=native_kids_set_exists rest n key old value h
    simp [Kids.set,hpost]
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
