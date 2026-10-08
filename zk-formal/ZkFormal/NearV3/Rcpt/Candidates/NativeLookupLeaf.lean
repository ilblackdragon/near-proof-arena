import ZkFormal.NearV3.Rcpt.Candidates.NativeForestMetadata
import ZkFormal.NearV3.Rcpt.Candidates.WalkRequestInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

def lookupDrain (key : List Nat) : List WStep3 :=
  (key++[SYM_END]).map (fun sym=>⟨3,sym,[0,0,0,0,0,0],0,0,0,0⟩)

def lookupEdge (mode sym : Nat) (e : Msg) : WStep3 := ⟨mode,sym,e,0,0,0,0⟩

/-- Arbitrary-key leaf lookup. An unresolved value yields no fabricated path. -/
def leafLookupSteps (nid vid : Nat) (slot : Slot) : Nat→List Nat→List Nat→Option (List WStep3)
  | pos,[],[]=>match slot with
    | .val _=>some [lookupEdge 0 SYM_END [nid,pos,SYM_END,vid,0,EK_VAL]]
    | .ref _ _=>none
  | pos,a::_,[]=>some [lookupEdge 1 SYM_END [nid,pos,a,nid,pos+1,EK_KEY]]
  | pos,[],x::xs=>some (lookupEdge 1 x [nid,pos,SYM_END,nid,pos,EK_LEND]::lookupDrain xs)
  | pos,a::as,x::xs=>if a=x then
      (leafLookupSteps nid vid slot (pos+1) as xs).map
        (lookupEdge 0 x [nid,pos,a,nid,pos+1,EK_KEY]::·)
    else some (lookupEdge 1 x [nid,pos,a,nid,pos+1,EK_KEY]::lookupDrain xs)

theorem lookupDrain_symbols (key : List Nat) : (lookupDrain key).map WStep3.sym=key++[SYM_END] := by
  simp [lookupDrain,List.map_map,Function.comp_def]

theorem leafLookupSteps_symbols (nid vid : Nat) (slot : Slot) :
    ∀pos stored key steps,leafLookupSteps nid vid slot pos stored key=some steps→
      steps.map WStep3.sym=key++[SYM_END]
  | pos,[],[],steps,h=>by
    cases slot <;> simp only [leafLookupSteps,Option.some.injEq,Option.noConfusion] at h
    · rw [←h];rfl
    · cases h
  | pos,a::as,[],steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h
    rw [←h];rfl
  | pos,[],x::xs,steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h
    rw [←h]
    simp [lookupEdge,lookupDrain_symbols]
  | pos,a::as,x::xs,steps,h=>by
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h
        subst steps
        simp only [List.map_cons,lookupEdge]
        rw [leafLookupSteps_symbols nid vid slot (pos+1) as xs tail ht]
        rfl
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h
      rw [←h]
      simp [lookupEdge,lookupDrain_symbols]

theorem leafLookupSteps_length (nid vid : Nat) (slot : Slot)
    (pos : Nat) (stored key : List Nat) (steps : List WStep3)
    (h : leafLookupSteps nid vid slot pos stored key=some steps) : steps.length=key.length+1 := by
  have hh:=congrArg List.length (leafLookupSteps_symbols nid vid slot pos stored key steps h)
  simpa using hh

/-- Definedness is exactly native proven lookup, including unknown references. -/
theorem leafLookupSteps_defined (nid vid : Nat) (slot : Slot) :
    ∀pos stored key,(leafLookupSteps nid vid slot pos stored key).isSome=
      ((PTrie.leaf stored slot 0).find key).isSome
  | pos,[],[]=>by cases slot <;> rfl
  | pos,a::as,[]=>by simp [leafLookupSteps,PTrie.find]
  | pos,[],x::xs=>by simp [leafLookupSteps,PTrie.find]
  | pos,a::as,x::xs=>by
    by_cases he : a=x
    · subst x
      simp only [leafLookupSteps,ite_true,Option.isSome_map]
      rw [leafLookupSteps_defined nid vid slot (pos+1) as xs]
      simp [PTrie.find]
    · simp [leafLookupSteps,PTrie.find,he]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
