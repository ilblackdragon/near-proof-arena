import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupCounters

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra

def lookupPayloadSmall (ss : List WStep3) : Prop := ∀s∈ss,∀x∈s.e,x<P

theorem lookupPayload_cons (s : WStep3) (ss : List WStep3)
    (hs : ∀x∈s.e,x<P) (ht : lookupPayloadSmall ss) : lookupPayloadSmall (s::ss) := by
  intro t hm;rcases List.mem_cons.mp hm with rfl|hm
  · exact hs
  · exact ht t hm

theorem lookupPayload_append (a b : List WStep3) (ha : lookupPayloadSmall a)
    (hb : lookupPayloadSmall b) : lookupPayloadSmall (a++b) := by
  intro s hs;rcases List.mem_append.mp hs with hs|hs
  · exact ha s hs
  · exact hb s hs

theorem lookupDrain_payload (key : List Nat) : lookupPayloadSmall (lookupDrain key) := by
  intro s hs;obtain ⟨a,_,rfl⟩:=List.mem_map.mp hs
  simp;decide

theorem leafLookupSteps_payload (nid vid : Nat) (slot : Slot) (hn : nid<P) (hv : vid<P) :
    ∀pos stored key steps,pos+stored.length<P→(∀a∈stored,a<16)→
      leafLookupSteps nid vid slot pos stored key=some steps→lookupPayloadSmall steps
  | pos,[],[],steps,hp,hs,h=>by
    cases slot with
    | ref l b=>cases h
    | val b=>
      simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h]
      have hp' : pos<P := by simpa using hp
      simp [lookupPayloadSmall,lookupEdge,hn,hv,hp',SYM_END,EK_VAL];decide
  | pos,a::as,[],steps,hp,hs,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h]
    have hp' : pos<P := by simp only [List.length_cons] at hp;omega
    have hp1 : pos+1<P := by simp only [List.length_cons] at hp;omega
    have ha : a<P := by have hh:=hs a (by simp);unfold P;omega
    simp [lookupPayloadSmall,lookupEdge,hn,hp',hp1,ha,EK_KEY];decide
  | pos,[],x::xs,steps,hp,hs,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h]
    apply lookupPayload_cons _ _ ?_ (lookupDrain_payload xs)
    have hp' : pos<P := by simpa using hp
    simp [lookupEdge,hn,hp',SYM_END,EK_LEND];decide
  | pos,a::as,x::xs,steps,hp,hs,h=>by
    have hp' : pos<P := by simp only [List.length_cons] at hp;omega
    have hp1 : pos+1<P := by simp only [List.length_cons] at hp;omega
    have ha : a<P := by have hh:=hs a (by simp);unfold P;omega
    have hec : ∀v∈(lookupEdge 0 x [nid,pos,a,nid,pos+1,EK_KEY]).e,v<P := by
      simp [lookupEdge,hn,hp',hp1,ha,EK_KEY];decide
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
        exact lookupPayload_cons _ _ (by simpa [he] using hec) (leafLookupSteps_payload nid vid slot hn hv (pos+1) as xs tail
          (by simp only [List.length_cons] at hp;omega) (fun b hb=>hs b (by simp [hb])) ht)
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h;rw [←h]
      exact lookupPayload_cons _ _ hec (lookupDrain_payload xs)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
