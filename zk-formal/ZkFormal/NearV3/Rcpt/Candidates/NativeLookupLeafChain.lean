import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupLeafHead

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

def lookupNext (s t : WStep3) : Prop :=
  (s.mode=0→t.e.take 2=(s.e.drop 3).take 2 ∧ t.mode≠3) ∧ (s.mode≠0→t.mode=3)
def lookupChain : List WStep3→Prop
  | []=>True
  | [_]=>True
  | s::t::rest=>lookupNext s t ∧ lookupChain (t::rest)

theorem lookupDrain_chain (key : List Nat) : lookupChain (lookupDrain key) := by
  induction key with
  | nil=>trivial
  | cons x xs ih=>
    cases xs with
    | nil=>constructor <;> simp [lookupDrain,lookupChain,lookupNext]
    | cons y ys=>exact ⟨by simp [lookupNext],ih⟩

theorem lookupDrain_cons_chain (s : WStep3) (hm : s.mode≠0) (key : List Nat) :
    lookupChain (s::lookupDrain key) := by
  have h:=lookupDrain_chain key
  cases key with
  | nil=>exact ⟨by simp [lookupNext,hm],h⟩
  | cons x xs=>exact ⟨by simp [lookupNext,hm],h⟩

theorem leafLookupSteps_chain (nid vid : Nat) (slot : Slot) :
    ∀pos stored key steps,leafLookupSteps nid vid slot pos stored key=some steps→lookupChain steps
  | pos,[],[],steps,h=>by
    cases slot with
    | ref l v=>cases h
    | val v=>simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h];trivial
  | pos,a::as,[],steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h];trivial
  | pos,[],x::xs,steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h]
    exact lookupDrain_cons_chain _ (by simp [lookupEdge]) xs
  | pos,a::as,x::xs,steps,h=>by
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h
        rw [←h]
        have hn:=leafLookupSteps_length nid vid slot (pos+1) as xs tail ht
        have hc:=leafLookupSteps_chain nid vid slot (pos+1) as xs tail ht
        cases tail with
        | nil=>simp at hn
        | cons s ss=>
          have hf:=leafLookupSteps_first nid vid slot (pos+1) as xs (s::ss) s ht rfl
          refine ⟨?_,hc⟩
          simp only [lookupNext,lookupEdge,List.drop_cons,List.drop_zero,List.take_succ_cons,List.take_zero,true_implies,ne_eq,not_true_eq_false,false_implies,and_true]
          exact ⟨hf.1,by omega⟩
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h;rw [←h]
      exact lookupDrain_cons_chain _ (by simp [lookupEdge]) xs

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
