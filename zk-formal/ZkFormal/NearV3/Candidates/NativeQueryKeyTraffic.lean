import ZkFormal.NearV3.Candidates.NativeQueryKey
namespace ZkFormal.NearV3.Candidates.NativeQueryKey
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate ZkFormal.Air ZkFormal.Algebra

theorem rank_key (previous : List WStep3) (w : WalkR) :
    walkRecvs3 [rankWalk previous w] B_KEYNIB=walkRecvs3 [w] B_KEYNIB := by
  simp only [walkRecvs3,show B_KEYNIB≠B_EDGE by decide,show B_KEYNIB≠B_BMAP by decide,
    ite_false,ite_true,List.flatMap_cons,List.flatMap_nil,List.append_nil,rankWalk_length]
  apply List.map_congr_left
  intro i _
  rw [(rankWalk_semantics previous w (i+1)).2.1]
  rfl

theorem ranks_key (previous : List WStep3) (ws : List WalkR) :
    walkRecvs3 (rankWalks previous ws) B_KEYNIB=walkRecvs3 ws B_KEYNIB := by
  induction ws generalizing previous with
  | nil=>rfl
  | cons w ws ih=>
    have h:=rank_key previous w
    simp only [walkRecvs3,show B_KEYNIB≠B_EDGE by decide,show B_KEYNIB≠B_BMAP by decide,
      ite_false,ite_true,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h
    change _++walkRecvs3 (rankWalks (previous++w.steps) ws) B_KEYNIB=_++walkRecvs3 ws B_KEYNIB
    dsimp only
    rw [h,ih]

theorem queries_key (pairs : List (PTrie×PTrie)) : ∀qs ws,
    nativeQueryWalks pairs qs=some ws→walkRecvs3 ws B_KEYNIB=
      qs.flatMap (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END]))
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
        have hi:=queries_key pairs qs tail ht
        have hk:=query_key pairs q w hq
        simp only [walkRecvs3,show B_KEYNIB≠B_EDGE by decide,show B_KEYNIB≠B_BMAP by decide,
          ite_false,ite_true,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hk
        change _++walkRecvs3 tail B_KEYNIB=_
        dsimp only
        rw [hk,hi]
        rfl

/-- Physical KEYNIB receives are exactly the native query keys, with END and
last-symbol flags; this counts repeated and absent lookups in full. -/
theorem physical_key (pairs : List (PTrie×PTrie)) (qs : List NativeLookupQuery) (ws : List WalkR)
    (h:nativeQueryWalks pairs qs=some ws) (previous : List WStep3)
    (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (ht:TableTraffic WalkV3.interactions tr tt pub (walkTraffic3 (rankWalks previous ws))) (msg : List Fp) :
    tableBusCount WalkV3.interactions tr tt pub B_KEYNIB false msg=
      ((qs.flatMap (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END]))).map Msg.toFp).count msg := by
  rw [(ht B_KEYNIB msg).2]
  change ((walkRecvs3 (rankWalks previous ws) B_KEYNIB).map Msg.toFp).count msg=_
  rw [ranks_key,queries_key pairs qs ws h]
end ZkFormal.NearV3.Candidates.NativeQueryKey
