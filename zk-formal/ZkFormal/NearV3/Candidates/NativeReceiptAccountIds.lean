import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountSlotVersions
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupWhole
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupValueProvider
import ZkFormal.NearV3.Assembly.RcptSkeletonPlan

namespace ZkFormal.NearV3.Candidates.NativeReceiptAccountIds
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- Receipt memory IDs use the same original-prestate occurrence indices as
account rows and native lookup walks, never scheduler-intermediate ordinals. -/
def accountId (pre : PTrie) (rs : List Receipt) (p : RcptSkeleton.ReceiptPlan) : Nat :=
  accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) p.receiptIndex

theorem query_at (rs : List Receipt) (j : Nat) (r : Receipt) (hj : rs[j]?=some r) :
    (accountLookupQueries rs)[j]?=some (⟨j,0,accountKeyPath r.receiverId⟩ : NativeLookupQuery) := by
  simp [accountLookupQueries,List.getElem?_map,List.getElem?_zipIdx,hj]

theorem query_result (pre post : PTrie) (rest : List (PTrie×PTrie))
    (j : Nat) (key : List Nat) (w : WalkR)
    (h : nativeQueryWalk ((pre,post)::rest) ⟨j,0,key⟩=some w) :
    w.steps.getLast?.map lookupFinal=some (valueIndex pre key) := by
  simp only [nativeQueryWalk,List.getElem?_cons_zero,List.take_zero,List.map_nil,
    bind,Option.bind] at h
  cases hs : nativeLookupSteps (forestLookupNid []) (forestLookupVid []) pre key with
  | none=>simp [hs] at h
  | some ss=>
    simp only [hs] at h
    change some (nativeLookupWalk j 0 (forestLookupNid []) pre ss)=some w at h
    have hw:=Option.some.inj h
    subst w
    have he:=nativeLookupWalk_valueIndex j 0 (forestLookupNid []) (forestLookupVid []) pre key ss hs
    simpa [forestLookupVid,forestBytes] using he

theorem slot_at {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h : nativeAccountViews pre post rs=some as) (j : Nat) (r : Receipt)
    (hj : rs[j]?=some r) :
    valueIndex pre (accountKeyPath r.receiverId)=some
      (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) j) := by
  have hm:=List.mem_of_getElem? hj
  obtain ⟨i,hi⟩:=nativeAccountViews_keys_defined h (accountKeyPath r.receiverId) (List.mem_map.mpr ⟨r,hm,rfl⟩)
  simp only [accountSlot,List.getD_eq_getElem?_getD,List.getElem?_map,hj,Option.map_some,Option.getD_some,hi]

/-- Every account query in the actual combined query list returns the original
prestate slot used by receipt memory, including repeated receiver queries. -/
theorem walks_slot {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (ha : nativeAccountViews pre post rs=some as)
    (queryPost : PTrie) (rest : List (PTrie×PTrie)) (suffix : List NativeLookupQuery) (ws : List WalkR)
    (hw : nativeQueryWalks ((pre,queryPost)::rest) (accountLookupQueries rs++suffix)=some ws)
    (j : Nat) (r : Receipt) (hj : rs[j]?=some r) :
    ∃w, ws[j]?=some w ∧ w.steps.getLast?.map lookupFinal=
      some (some (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) j)) := by
  have hq:=query_at rs j r hj
  have hjq : j<(accountLookupQueries rs).length := by
    cases Nat.lt_or_ge j (accountLookupQueries rs).length with
    | inl h=>exact h
    | inr h=>
      have hz : (accountLookupQueries rs)[j]?=none := List.getElem?_eq_none h
      rw [hz] at hq
      contradiction
  have he:=congrArg (fun xs=>xs[j]?)
    (nativeQueryWalks_exact ((pre,queryPost)::rest) (accountLookupQueries rs++suffix) ws hw)
  simp only [List.getElem?_map,List.getElem?_append_left hjq,hq,Option.map_some] at he
  cases hs : ws[j]? with
  | none=>simp [hs] at he
  | some w=>
    simp only [hs,Option.map_some,Option.some.injEq] at he
    refine ⟨w,rfl,?_⟩
    rw [query_result pre queryPost rest j (accountKeyPath r.receiverId) w he.symm,slot_at ha j r hj]

end ZkFormal.NearV3.Candidates.NativeReceiptAccountIds
