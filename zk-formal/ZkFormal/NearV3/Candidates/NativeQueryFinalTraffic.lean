import ZkFormal.NearV3.Candidates.NativeQueryFinal
import ZkFormal.NearV3.Rcpt.Candidates.WalkRanksWf
namespace ZkFormal.NearV3.Candidates.NativeQueryFinal
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate ZkFormal.Air ZkFormal.Algebra

theorem rank_fields (previous : List WStep3) (w : WalkR) :
    (rankWalk previous w).fk=w.fk ∧ (rankWalk previous w).k=w.k := by
  have h:=rankWalk_semantics previous w (w.steps.length-1)
  simp only [WalkR.fk,WalkR.k,WalkR.last,rankWalk_length,h.1,h.2.2.1]
  exact ⟨rfl,rfl⟩

theorem ranks_final (previous : List WStep3) (ws : List WalkR) :
    walkSends3 (rankWalks previous ws) B_FINAL=walkSends3 ws B_FINAL := by
  simp only [walkSends3,show B_FINAL≠B_EDGE by decide,show B_FINAL≠B_BMAP by decide,ite_false,ite_true]
  induction ws generalizing previous with
  | nil=>rfl
  | cons w ws ih=>
    simp only [rankWalks,List.map_cons,(rank_fields previous w).1,(rank_fields previous w).2]
    rw [ih]
    rfl

theorem queries_final (pairs : List (PTrie×PTrie)) : ∀qs ws,
    nativeQueryWalks pairs qs=some ws→walkSends3 ws B_FINAL=qs.map (queryMessage pairs)
  | [],ws,h=>by cases h;rfl
  | q::qs,ws,h=>by
    cases hq:nativeQueryWalk pairs q with
    | none=>simp [nativeQueryWalks,hq] at h
    | some w=>
      cases ht:nativeQueryWalks pairs qs with
      | none=>simp [nativeQueryWalks,hq,ht] at h
      | some tail=>
        simp [nativeQueryWalks,hq,ht] at h
        subst ws
        have hi:=queries_final pairs qs tail ht
        change [w.w,w.tau,w.fk,w.k]::walkSends3 tail B_FINAL=_
        rw [query_message pairs q w hq,hi]
        rfl

/-- Actual physical FINAL traffic for the caller's SAME native query list,
after the shared EDGE/BMAP counters are assigned. -/
theorem physical_final (pairs : List (PTrie×PTrie)) (qs : List NativeLookupQuery) (ws : List WalkR)
    (h:nativeQueryWalks pairs qs=some ws) (previous : List WStep3)
    (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (ht:TableTraffic WalkV3.interactions tr tt pub (walkTraffic3 (rankWalks previous ws))) (msg : List Fp) :
    tableBusCount WalkV3.interactions tr tt pub B_FINAL true msg=
      ((qs.map (queryMessage pairs)).map Msg.toFp).count msg := by
  rw [(ht B_FINAL msg).1]
  change ((walkSends3 (rankWalks previous ws) B_FINAL).map Msg.toFp).count msg=_
  rw [ranks_final,queries_final pairs qs ws h]
end ZkFormal.NearV3.Candidates.NativeQueryFinal
