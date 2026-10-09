import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupLeaf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

def lookupFinal (st : WStep3) : Option Nat := if st.mode=0 then some (st.e.getD 3 0) else none

theorem lookupDrain_last (key : List Nat) :
    (lookupDrain key).getLast?=some ⟨3,SYM_END,[0,0,0,0,0,0],0,0,0,0⟩ := by
  simp [lookupDrain,List.getLast?_map,List.getLast?_append]

private theorem cons_last {α : Type} (x : α) (xs : List α) (h : 0<xs.length) :
    (x::xs).getLast?=xs.getLast? := by
  cases xs with
  | nil=>simp at h
  | cons y ys=>rw [List.getLast?_cons_cons]

theorem leafLookupSteps_final (nid vid : Nat) (slot : Slot) :
    ∀pos stored key steps,leafLookupSteps nid vid slot pos stored key=some steps→
      steps.getLast?.map lookupFinal=some (if stored=key then some vid else none)
  | pos,[],[],steps,h=>by
    cases slot with
    | val v=>simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h];rfl
    | ref l v=>cases h
  | pos,a::as,[],steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h
    rw [←h]
    simp [lookupFinal,lookupEdge]
  | pos,[],x::xs,steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h
    rw [←h,List.getLast?_cons,lookupDrain_last]
    simp [lookupFinal]
  | pos,a::as,x::xs,steps,h=>by
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h
        rw [←h,cons_last _ tail (by have hh:=leafLookupSteps_length nid vid slot (pos+1) as xs tail ht;omega)]
        rw [leafLookupSteps_final nid vid slot (pos+1) as xs tail ht]
        simp [he]
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h
      rw [←h,List.getLast?_cons,lookupDrain_last]
      simp [lookupFinal,he]

/-- The constructed terminal denotes the actual native leaf lookup result. -/
theorem leafLookupSteps_native_final (nid vid : Nat) (slot : Slot) (mem pos : Nat)
    (stored key : List Nat) (steps : List WStep3)
    (h : leafLookupSteps nid vid slot pos stored key=some steps) :
    steps.getLast?.map lookupFinal=
      ((PTrie.leaf stored slot mem).find key).map (fun value=>value.map (fun _=>vid)) := by
  rw [leafLookupSteps_final nid vid slot pos stored key steps h]
  by_cases he : stored=key
  · subst key
    have hd:=leafLookupSteps_defined nid vid slot pos stored stored
    rw [h] at hd
    cases slot <;> simp_all [PTrie.find,Slot.get]
  · simp [PTrie.find,he]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
