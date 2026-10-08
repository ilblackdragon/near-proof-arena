import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupKeyBounds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

theorem lookupExtensionEdges_payload (nid target : Nat) (key : List Nat)
    (hn : nid<P) (ht : target<P) (hl : key.length<P) (hk : ∀a∈key,a<16) :
    lookupPayloadSmall (lookupExtensionEdges nid target key) := by
  intro s hs;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hs
  have hi' : i<key.length := List.mem_range.mp hi
  have hnib : key.getD i 0<P := by
    have hh:=hk key[i] (List.getElem_mem hi')
    have he : key.getD i 0=key[i] := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi']
    rw [he];unfold P;omega
  have hiP : i<P := by omega
  have hi1P : i+1<P := by omega
  have ht' : (if i+1=key.length then target else nid)<P := by split <;> assumption
  have hp' : (if i+1=key.length then 0 else i+1)<P := by
    split
    · decide
    · exact hi1P
  simp [lookupEdge,hn,hiP,ht',hp',EK_KEY]
  exact ⟨hnib,by decide⟩

theorem lookupBranchAbsent_payload (nid bm hv sym : Nat) (key : List Nat) (hn : nid<P) :
    lookupPayloadSmall (lookupBranchAbsent nid bm hv sym key) := by
  apply lookupPayload_cons _ _ ?_ (lookupDrain_payload key)
  simp [hn];decide

mutual
theorem nativeLookupSteps_payload (nid vid : Nat) : ∀tree key steps,
    tree.wf=true→nid+tsize tree<P→vid+(valsOf tree).length<P→
    (∀o∈occs tree,nativeStoredKeyLength o<P)→(∀a∈key,a<16)→
    nativeLookupSteps nid vid tree key=some steps→lookupPayloadSmall steps
  | .hash _,_,_,_,_,_,_,_,h=>by cases h
  | .leaf stored slot mem,key,steps,hw,hn,hv,hl,hk,h=>by
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hs : ∀a∈stored,a<16 := by simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    apply leafLookupSteps_payload nid vid slot (by omega) (by omega) 0 stored key steps ?_ hs h
    simpa [nativeStoredKeyLength] using hl (.leaf stored slot mem) (by simp [occs])
  | .ext stored child mem,key,steps,hw,hn,hv,hl,hk,h=>by
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hs : ∀a∈stored,a<16 := by simpa [nibblesOk,List.all_eq_true] using hw.1.1.1
    have hn' : nid+1+tsize child<P := by simpa [tsize,occs,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hn
    have hv' : vid+(valsOf child).length<P := by simpa [valsOf_ext] using hv
    have hl' : stored.length<P := hl (.ext stored child mem) (by simp [occs])
    cases hp : isPrefix stored key with
    | false=>
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
      cases he : leafLookupSteps nid vid (.ref 0 []) 0 stored key with
      | none=>simp [he] at h
      | some raw=>
        simp only [he,Option.map_some,Option.some.injEq] at h;rw [←h]
        exact extensionMismatchFix_payload nid child stored.length raw hn'
          (leafLookupSteps_payload nid vid (.ref 0 []) (by omega) (by omega) 0 stored key raw
            (by simpa using hl') hs he)
    | true=>
      simp only [nativeLookupSteps,hp,ite_true] at h
      cases ht : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
        apply lookupPayload_append
        · have hb:=target_bound child (nid+1) (nativeLookupSteps_isNode (nid+1) vid child _ tail ht)
          exact lookupExtensionEdges_payload nid _ stored (by omega) (by omega) hl' hs
        · exact nativeLookupSteps_payload (nid+1) vid child _ tail hw.1.1.2 hn' hv'
            (fun o ho=>hl o (by simp [occs,ho])) (fun a ha=>hk a (List.mem_of_mem_drop ha)) ht
  | .branch value kids mem,[],steps,hw,hn,hv,hl,hk,h=>by
    have hn' : nid<P := by omega
    have hv' : vid<P := by omega
    cases value with
    | none=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupPayloadSmall,hn'];decide
    | some v=>cases v with
      | ref l b=>cases h
      | val b=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupPayloadSmall,lookupEdge,hn',hv',SYM_END,EK_VAL];decide
  | .branch value kids mem,x::xs,steps,hw,hn,hv,hl,hk,h=>by
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hn' : nid+1+ksize kids<P := by simpa [tsize,ksize,occs,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hn
    have hv' : vid+(optSlotVal value).length+(kvals kids).length<P := by simpa [valsOf_branch,List.length_append,Nat.add_assoc] using hv
    exact nativeKidsLookupSteps_payload nid _ _ x (nid+1) _ kids 16 x xs steps hw.1.2
      (by omega) (by have hx:=hk x (by simp);unfold P;omega) hn' hv'
      (fun o ho=>hl o (by simp [occs,ho])) (fun a ha=>hk a (by simp [ha])) h

theorem nativeKidsLookupSteps_payload (parent bm hv sym nid vid : Nat) : ∀kids n j key steps,
    Kids.wf kids n=true→parent<P→sym<P→nid+ksize kids<P→vid+(kvals kids).length<P→
    (∀o∈kOccs kids,nativeStoredKeyLength o<P)→(∀a∈key,a<16)→
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some steps→lookupPayloadSmall steps
  | .nil,n,j,key,steps,hw,hp,hs,hn,hv',hl,hk,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h]
    exact lookupBranchAbsent_payload parent bm hv sym key hp
  | .none rest,n,0,key,steps,hw,hp,hs,hn,hv',hl,hk,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h]
    exact lookupBranchAbsent_payload parent bm hv sym key hp
  | .some child rest,n,0,key,steps,hw,hp,hs,hn,hv',hl,hk,h=>by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    have hn' : nid+tsize child<P := by simp only [ksize,kOccs,List.length_append] at hn;change nid+(occs child).length<P;omega
    have hv'' : vid+(valsOf child).length<P := by simp only [kvals_some,List.length_append] at hv';omega
    simp only [nativeKidsLookupSteps] at h
    cases ht : nativeLookupSteps nid vid child key with
    | none=>simp [ht] at h
    | some tail=>
      simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
      apply lookupPayload_cons
      · have hb:=target_bound child nid (nativeLookupSteps_isNode nid vid child key tail ht)
        have htarget : viewTarget nid child<P := by omega
        simp [lookupEdge,hp,hs,htarget,EK_DOWN];decide
      · exact nativeLookupSteps_payload nid vid child key tail hw.1.2 hn' hv''
          (fun o ho=>hl o (by simp [kOccs,ho])) hk ht
  | .none rest,n,j+1,key,steps,hw,hp,hs,hn,hv',hl,hk,h=>by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    exact nativeKidsLookupSteps_payload parent bm hv sym nid vid rest (n-1) j key steps
      hw.2 hp hs hn hv' hl hk h
  | .some child rest,n,j+1,key,steps,hw,hp,hs,hn,hv',hl,hk,h=>by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    apply nativeKidsLookupSteps_payload parent bm hv sym (nid+tsize child) (vid+(valsOf child).length)
      rest (n-1) j key steps hw.2 hp hs ?_ ?_ ?_ hk h
    · simpa [ksize,tsize,kOccs,List.length_append,Nat.add_assoc] using hn
    · simpa [kvals_some,List.length_append,Nat.add_assoc] using hv'
    · intro o ho;exact hl o (by simp [kOccs,ho])
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
