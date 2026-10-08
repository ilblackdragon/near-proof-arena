import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupLeafFinal

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

def lookupRows : List WStep3→Prop
  | []=>True
  | [s]=>StepOk s true
  | s::t::rest=>StepOk s false ∧ lookupRows (t::rest)

theorem lookupDrain_rows (key : List Nat) : lookupRows (lookupDrain key) := by
  induction key with
  | nil=>constructor <;> simp [lookupDrain,lookupRows]
  | cons x xs ih=>
    have hn : lookupDrain xs≠[] := by
      intro he
      have hh:=lookupDrain_symbols xs
      rw [he] at hh
      simp at hh
    have hh : lookupDrain (x::xs)=⟨3,x,[0,0,0,0,0,0],0,0,0,0⟩::lookupDrain xs := rfl
    rw [hh]
    cases ht : lookupDrain xs with
    | nil=>exact False.elim (hn ht)
    | cons y ys=>
      change StepOk _ false ∧ _
      refine ⟨?_,by simpa [ht] using ih⟩
      constructor <;> simp

private theorem rows_cons (s : WStep3) (ss : List WStep3) (hn : 0<ss.length)
    (hs : StepOk s false) (ht : lookupRows ss) : lookupRows (s::ss) := by
  cases ss with
  | nil=>simp at hn
  | cons t rest=>exact ⟨hs,ht⟩

theorem leafLookupSteps_rows (nid vid : Nat) (slot : Slot) :
    ∀pos stored key steps,(∀a∈stored,a<16)→(∀a∈key,a<16)→
      leafLookupSteps nid vid slot pos stored key=some steps→lookupRows steps
  | pos,[],[],steps,hs,hk,h=>by
    cases slot with
    | val v=>
      simp only [leafLookupSteps,Option.some.injEq] at h
      rw [←h]
      constructor <;> simp [lookupEdge,EK_VAL]
    | ref l v=>cases h
  | pos,a::as,[],steps,hs,hk,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h
    rw [←h]
    have ha:=hs a (by simp)
    constructor <;> simp [lookupEdge,SYM_END,EK_KEY] <;> omega
  | pos,[],x::xs,steps,hs,hk,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h
    rw [←h]
    have hx:=hk x (by simp)
    apply rows_cons
    · simp [lookupDrain]
    · constructor <;> simp [lookupEdge,SYM_END,EK_LEND] <;> omega
    · exact lookupDrain_rows xs
  | pos,a::as,x::xs,steps,hs,hk,h=>by
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h
        rw [←h]
        apply rows_cons
        · have hh:=leafLookupSteps_length nid vid slot (pos+1) as xs tail ht;omega
        · constructor <;> simp [lookupEdge,he,EK_KEY]
        · exact leafLookupSteps_rows nid vid slot (pos+1) as xs tail
            (fun b hb=>hs b (by simp [hb])) (fun b hb=>hk b (by simp [hb])) ht
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h
      rw [←h]
      apply rows_cons
      · simp [lookupDrain]
      · constructor <;> simp [lookupEdge,he,EK_KEY]
      · exact lookupDrain_rows xs

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
