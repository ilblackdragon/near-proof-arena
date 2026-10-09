import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly Qv Qv.Candidates.CombinedWalkGen

theorem queue_lookup_rows (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) :
    ((queueLookupQueries pre v pres resolve).map (fun q=>q.key.length+2)).sum=
      12+20*v.shards.length+4*pres.length := by
  simp [queueLookupQueries,queueLookupQuery,plan,mainPlan,implicitPlan,mainWalk,
    Walk.request,Kind.bytes,nibbles_length,List.map_map,Function.comp_def,u64,NearSpec.leN_length,List.map_const',List.sum_replicate_nat]
  omega

theorem native_queue_rows (pairs : List (PTrie×PTrie)) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (resolve : Resolve) (ws : List WalkR)
    (h : nativeQueryWalks pairs (queueLookupQueries pre v pres resolve)=some ws) :
    (ws.flatMap (·.steps)).length=12+20*v.shards.length+4*pres.length := by
  rw [nativeQueryWalks_rows pairs _ ws h,queue_lookup_rows]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
