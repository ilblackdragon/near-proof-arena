import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupExtensionRegression

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near

/-- A failed prefix reads only actual stored-key edges. A matched edge before
that failure cannot be the last stored-key edge. -/
theorem leaf_mismatch_shape (nid vid : Nat) (slot : Slot) :
    ∀stored pos key steps,isPrefix stored key=false→
      leafLookupSteps nid vid slot pos stored key=some steps→
      ∀s∈steps,s.mode≤1→∃j,j<stored.length ∧
        s.e=[nid,pos+j,stored.getD j 0,nid,pos+j+1,EK_KEY] ∧
        (s.mode=0→j+1<stored.length)
  | [],_,_,_,hp,_,_,_,_=>by cases hp
  | a::as,pos,[],steps,hp,h,s,hm,hmode=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h] at hm
    simp only [List.mem_singleton] at hm;subst s
    exact ⟨0,by simp,by simp [lookupEdge],by simp [lookupEdge]⟩
  | a::as,pos,x::xs,steps,hp,h,s,hm,hmode=>by
    by_cases he : a=x
    · have hp' : isPrefix as xs=false := by simpa [isPrefix,he] using hp
      have hlen : 0<as.length := by cases as <;> simp_all [isPrefix]
      simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h] at hm
        rcases List.mem_cons.mp hm with rfl|hm
        · refine ⟨0,by simp,?_,?_⟩
          · simp [lookupEdge,he]
          · simp only [List.length_cons];omega
        · obtain ⟨j,hj,hej,hjlast⟩:=leaf_mismatch_shape nid vid slot as (pos+1) xs tail hp' ht s hm hmode
          refine ⟨j+1,by simp;omega,?_,?_⟩
          · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hej
          · simp only [List.length_cons];intro hm;have hh:=hjlast hm;omega
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h;rw [←h] at hm
      rcases List.mem_cons.mp hm with rfl|hm
      · exact ⟨0,by simp,by simp [lookupEdge],by simp [lookupEdge]⟩
      · exact False.elim (lookupDrain_no_edges xs s hm hmode)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
