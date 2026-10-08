import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupWalk

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

def lookupZeroUses (ss : List WStep3) : Prop := ∀s∈ss,s.u=0 ∧ s.ub=0

private theorem zero_cons (s : WStep3) (ss : List WStep3) (hs : s.u=0 ∧ s.ub=0)
    (ht : lookupZeroUses ss) : lookupZeroUses (s::ss) := by
  intro t hm;rcases List.mem_cons.mp hm with rfl|hm
  · exact hs
  · exact ht t hm

private theorem zero_append (a b : List WStep3) (ha : lookupZeroUses a) (hb : lookupZeroUses b) :
    lookupZeroUses (a++b) := by
  intro s hs;rcases List.mem_append.mp hs with hs|hs
  · exact ha s hs
  · exact hb s hs

theorem lookupDrain_zero (key : List Nat) : lookupZeroUses (lookupDrain key) := by
  intro s hs
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp hs
  exact ⟨rfl,rfl⟩

theorem leafLookupSteps_zero (nid vid : Nat) (slot : Slot) :
    ∀pos stored key steps,leafLookupSteps nid vid slot pos stored key=some steps→lookupZeroUses steps
  | pos,[],[],steps,h=>by
    cases slot with
    | ref l b=>cases h
    | val b=>simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupZeroUses,lookupEdge]
  | pos,a::as,[],steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupZeroUses,lookupEdge]
  | pos,[],x::xs,steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h]
    exact zero_cons _ _ ⟨rfl,rfl⟩ (lookupDrain_zero xs)
  | pos,a::as,x::xs,steps,h=>by
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
        exact zero_cons _ _ ⟨rfl,rfl⟩ (leafLookupSteps_zero nid vid slot (pos+1) as xs tail ht)
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h;rw [←h]
      exact zero_cons _ _ ⟨rfl,rfl⟩ (lookupDrain_zero xs)

mutual
theorem nativeLookupSteps_zero (nid vid : Nat) : ∀tree key steps,
    nativeLookupSteps nid vid tree key=some steps→lookupZeroUses steps
  | .hash _,_,_,h=>by cases h
  | .leaf stored slot mem,key,steps,h=>leafLookupSteps_zero nid vid slot 0 stored key steps h
  | .ext stored child mem,key,steps,h=>by
    cases hp : isPrefix stored key with
    | false=>
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
      exact leafLookupSteps_zero nid vid (.ref 0 []) 0 stored key steps h
    | true=>
      simp only [nativeLookupSteps,hp,ite_true] at h
      cases ht : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
        apply zero_append
        · intro s hs;obtain ⟨i,_,rfl⟩:=List.mem_map.mp hs;exact ⟨rfl,rfl⟩
        · exact nativeLookupSteps_zero (nid+1) vid child _ tail ht
  | .branch value kids mem,[],steps,h=>by
    cases value with
    | none=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupZeroUses]
    | some v=>cases v with
      | ref l b=>cases h
      | val b=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupZeroUses,lookupEdge]
  | .branch value kids mem,x::xs,steps,h=>nativeKidsLookupSteps_zero _ _ _ _ _ _ kids x xs steps h

theorem nativeKidsLookupSteps_zero (parent bm hv sym nid vid : Nat) : ∀kids j key steps,
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some steps→lookupZeroUses steps
  | .nil,_,key,steps,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h]
    exact zero_cons _ _ ⟨rfl,rfl⟩ (lookupDrain_zero key)
  | .none _,0,key,steps,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h]
    exact zero_cons _ _ ⟨rfl,rfl⟩ (lookupDrain_zero key)
  | .some child _,0,key,steps,h=>by
    simp only [nativeKidsLookupSteps] at h
    cases ht : nativeLookupSteps nid vid child key with
    | none=>simp [ht] at h
    | some tail=>
      simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
      exact zero_cons _ _ ⟨rfl,rfl⟩ (nativeLookupSteps_zero nid vid child key tail ht)
  | .none rest,j+1,key,steps,h=>nativeKidsLookupSteps_zero parent bm hv sym nid vid rest j key steps h
  | .some child rest,j+1,key,steps,h=>nativeKidsLookupSteps_zero parent bm hv sym
      (nid+tsize child) (vid+(valsOf child).length) rest j key steps h
end

theorem nativeLookupSteps_scalar_canon (nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (hk : ∀a∈key,a<16) (h : nativeLookupSteps nid vid tree key=some steps) :
    ∀s∈steps,s.sym<P ∧ s.u<P ∧ s.ub<P := by
  intro s hs
  have hz:=nativeLookupSteps_zero nid vid tree key steps h s hs
  have hsym : s.sym∈key++[SYM_END] := by
    rw [←nativeLookupSteps_symbols nid vid tree key steps h]
    exact List.mem_map.mpr ⟨s,hs,rfl⟩
  have hb : s.sym≤16 := by
    rcases List.mem_append.mp hsym with hm|hm
    · have hh:=hk _ hm;omega
    · simp only [List.mem_singleton,SYM_END] at hm;omega
  exact ⟨by unfold P;omega,by rw [hz.1];decide,by rw [hz.2];decide⟩

/-- Full walk validity with only the remaining edge payload range obligation. -/
theorem nativeLookupWalk_wf_of_payload (wid tau nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (hw : tree.wf=true) (hk : ∀a∈key,a<16)
    (h : nativeLookupSteps nid vid tree key=some steps)
    (hwid : wid<P) (htau : tau<P) (hcount : nid+tsize tree≤P)
    (he : ∀s∈steps,∀x∈s.e,x<P) (hn : key.length+2≤2^23) :
    WalkWf3 [nativeLookupWalk wid tau nid tree steps] := by
  have hb:=target_bound tree nid (nativeLookupSteps_isNode nid vid tree key steps h)
  have hroot : viewTarget nid tree<P := by omega
  apply nativeLookupWalk_wf wid tau nid vid tree key steps hw hk h hwid htau hroot ?_ hn
  intro s hs
  have hc:=nativeLookupSteps_scalar_canon nid vid tree key steps hk h s hs
  exact ⟨hc.1,hc.2.1,hc.2.2,he s hs⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
