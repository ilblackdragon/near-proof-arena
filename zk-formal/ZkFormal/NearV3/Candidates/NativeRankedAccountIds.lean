import ZkFormal.NearV3.Candidates.NativeReceiptAccountIds
import ZkFormal.NearV3.Rcpt.Candidates.WalkRanks

namespace ZkFormal.NearV3.Candidates.NativeRankedAccountIds
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem final_preserved (previous : List WStep3) (w : WalkR) :
    (rankWalk previous w).steps.getLast?.map lookupFinal=w.steps.getLast?.map lookupFinal := by
  rw [List.getLast?_eq_getElem?,List.getLast?_eq_getElem?,rankWalk_length]
  by_cases h:w.steps.length-1<w.steps.length
  · have hr : w.steps.length-1<(rankWalk previous w).steps.length := by simpa [rankWalk_length] using h
    simp only [List.getElem?_eq_getElem h,List.getElem?_eq_getElem hr,Option.map_some]
    rw [rankWalk_at previous w _ h]
    rfl
  · have hn : w.steps.length=0 := by omega
    have hr : (rankWalk previous w).steps.length=0 := by rw [rankWalk_length,hn]
    simp [List.getElem?_eq_none (by omega : w.steps.length≤w.steps.length-1),
      List.getElem?_eq_none (by omega : (rankWalk previous w).steps.length≤w.steps.length-1)]

theorem ranked_at : ∀(ws : List WalkR)(previous : List WStep3)(j : Nat)(w : WalkR),
    ws[j]?=some w→∃p,(rankWalks previous ws)[j]?=some (rankWalk p w)
  | [],_,_,_,h=>by simp at h
  | w::ws,previous,0,v,h=>by
    simp only [List.getElem?_cons_zero,Option.some.injEq] at h
    subst v
    exact ⟨previous,rfl⟩
  | w::ws,previous,j+1,v,h=>by
    exact ranked_at ws (previous++w.steps) j v h

/-- Counter assignment preserves the authenticated account slot at the same
receipt occurrence index in the actual rendered walk list. -/
theorem ranked_slot {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (ha : nativeAccountViews pre post rs=some as)
    (queryPost : PTrie) (rest : List (PTrie×PTrie)) (suffix : List NativeLookupQuery)
    (ws : List WalkR) (previous : List WStep3)
    (hw : nativeQueryWalks ((pre,queryPost)::rest) (accountLookupQueries rs++suffix)=some ws)
    (j : Nat) (r : Receipt) (hj : rs[j]?=some r) :
    ∃w,(rankWalks previous ws)[j]?=some w ∧ w.steps.getLast?.map lookupFinal=
      some (some (accountSlot pre (rs.map (fun r=>accountKeyPath r.receiverId)) j)) := by
  obtain ⟨w,hw,hv⟩:=NativeReceiptAccountIds.walks_slot ha queryPost rest suffix ws hw j r hj
  obtain ⟨p,hp⟩:=ranked_at ws previous j w hw
  exact ⟨rankWalk p w,hp,by rw [final_preserved,hv]⟩

end ZkFormal.NearV3.Candidates.NativeRankedAccountIds
