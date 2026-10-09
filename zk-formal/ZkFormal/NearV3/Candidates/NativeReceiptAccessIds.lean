import ZkFormal.NearV3.Candidates.NativeRankedAccountIds
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccessKeyQueries
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountReadPair

namespace ZkFormal.NearV3.Candidates.NativeReceiptAccessIds
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

def accessId (pre : PTrie) (p : RcptSkeleton.ReceiptPlan) : Option Nat :=
  valueIndex pre (keyAccessKey p.input.receipt.receiverId p.input.receipt.signerPk)

theorem query_mem (rs : List Receipt) (j : Nat) (r : Receipt)
    (hj : rs[j]?=some r) (hs : r.predecessorId=AccountId.system)
    (he : r.signerId=r.receiverId) :
    (⟨W_AK+j,0,keyAccessKey r.receiverId r.signerPk⟩ : NativeLookupQuery)∈accessKeyLookupQueries rs := by
  apply List.mem_map.mpr
  refine ⟨(r,j),List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hj,?_⟩,rfl⟩
  simp [hs,he]

theorem query_identity (pre post : PTrie) (rest : List (PTrie×PTrie))
    (wid : Nat) (key : List Nat) (w : WalkR)
    (h : nativeQueryWalk ((pre,post)::rest) ⟨wid,0,key⟩=some w) : w.w=wid := by
  simp only [nativeQueryWalk,List.getElem?_cons_zero,List.take_zero,List.map_nil,
    bind,Option.bind] at h
  cases hs : nativeLookupSteps (forestLookupNid []) (forestLookupVid []) pre key with
  | none=>simp [hs] at h
  | some ss=>
    simp only [hs] at h
    change some (nativeLookupWalk wid 0 (forestLookupNid []) pre ss)=some w at h
    have hw:=Option.some.inj h
    subst w
    rfl

/-- The refund lookup is selected by its original receipt ID even though the
conditional access-key query sublist is filtered. -/
theorem walks_slot (pre post : PTrie) (rest : List (PTrie×PTrie))
    (rs : List Receipt) (before after : List NativeLookupQuery) (ws : List WalkR)
    (hw : nativeQueryWalks ((pre,post)::rest) (before++accessKeyLookupQueries rs++after)=some ws)
    (j : Nat) (r : Receipt) (hj : rs[j]?=some r)
    (hs : r.predecessorId=AccountId.system) (he : r.signerId=r.receiverId) :
    ∃w∈ws,w.w=W_AK+j ∧ w.steps.getLast?.map lookupFinal=
      some (valueIndex pre (keyAccessKey r.receiverId r.signerPk)) := by
  let q : NativeLookupQuery:=⟨W_AK+j,0,keyAccessKey r.receiverId r.signerPk⟩
  have hq:q∈before++accessKeyLookupQueries rs++after:=
    List.mem_append_left _ (List.mem_append_right _ (query_mem rs j r hj hs he))
  have hx:nativeQueryWalk ((pre,post)::rest) q∈ws.map some := by
    rw [nativeQueryWalks_exact _ _ ws hw]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  obtain ⟨walk,hm,hwalk⟩:=List.mem_map.mp hx
  exact ⟨walk,hm,query_identity pre post rest _ _ walk hwalk.symm,
    NativeReceiptAccountIds.query_result pre post rest _ _ walk hwalk.symm⟩

theorem ranked_slot (pre post : PTrie) (rest : List (PTrie×PTrie))
    (rs : List Receipt) (before after : List NativeLookupQuery) (ws : List WalkR)
    (previous : List WStep3)
    (hw : nativeQueryWalks ((pre,post)::rest) (before++accessKeyLookupQueries rs++after)=some ws)
    (j : Nat) (r : Receipt) (hj : rs[j]?=some r)
    (hs : r.predecessorId=AccountId.system) (he : r.signerId=r.receiverId) :
    ∃w∈rankWalks previous ws,w.w=W_AK+j ∧ w.steps.getLast?.map lookupFinal=
      some (valueIndex pre (keyAccessKey r.receiverId r.signerPk)) := by
  obtain ⟨w,hm,hi,hv⟩:=walks_slot pre post rest rs before after ws hw j r hj hs he
  obtain ⟨i,he⟩:=List.mem_iff_getElem?.mp hm
  obtain ⟨p,hp⟩:=NativeRankedAccountIds.ranked_at ws previous i w he
  exact ⟨rankWalk p w,List.mem_of_getElem? hp,hi,by rw [NativeRankedAccountIds.final_preserved,hv]⟩

/-- Access-key bytes are fetched at the original VID; a successfully proved
absence has no byte provider and must retain the receipt absence flag. -/
theorem bytes_at {pre : PTrie} {key : List Nat} {i : Nat}
    (hi : valueIndex pre key=some i) :
    ∃bytes,pre.find key=some (some bytes) ∧ (NearSpecV3.valsOf pre)[i]?=some bytes := by
  obtain ⟨bytes,hb⟩:=valueIndex_defined pre key i hi
  obtain ⟨j,hj,hbytes⟩:=valueIndex_complete pre key bytes hb
  have he:i=j:=Option.some.inj (hi.symm.trans hj)
  subst j
  exact ⟨bytes,hb,hbytes⟩

theorem accepted_resolved {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hm : m.NativeValid k w) (r : Receipt) (hr : r∈appliedReceipts k w)
    (hs : r.predecessorId=AccountId.system) (he : r.signerId=r.receiverId) :
    ∃b,m.pre.find (keyAccessKey r.receiverId r.signerPk)=some b ∧
      (valueIndex m.pre (keyAccessKey r.receiverId r.signerPk)).isSome=b.isSome := by
  have hw : m.pre.wf=true := by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  have hk:=newchunk_access_keys_prestate (TrieShape.of_wf _ hw) hm.run r hr hs he
  cases hf:m.pre.find (keyAccessKey r.receiverId r.signerPk) with
  | none=>exact False.elim (hk hf)
  | some bytes=>
    refine ⟨bytes,rfl,?_⟩
    cases bytes with
    | none=>
      cases hi:valueIndex m.pre (keyAccessKey r.receiverId r.signerPk) with
      | none=>rfl
      | some i=>
        obtain ⟨b,hb⟩:=valueIndex_defined m.pre _ i hi
        rw [hf] at hb
        cases Option.some.inj hb
    | some bytes=>
      obtain ⟨i,hi,_⟩:=valueIndex_complete m.pre _ bytes hf
      simp [hi]

end ZkFormal.NearV3.Candidates.NativeReceiptAccessIds
