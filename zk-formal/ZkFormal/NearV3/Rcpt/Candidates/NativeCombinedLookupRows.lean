import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountQueryRows
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupJointInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly ZkFormal.Near Qv Qv.Candidates.CombinedWalkGen

/-- Receiver, queue and UPS walk rows together. Access-key traffic is not
included in this inventory and must be accounted for separately if generated. -/
theorem combined_lookup_rows (pairs : List (PTrie×PTrie)) (rs : List Receipt)
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (accounts queues : List WalkR) (Is : List Render.UpsInst)
    (ha : nativeQueryWalks pairs (accountLookupQueries rs)=some accounts)
    (hq : nativeQueryWalks pairs (queueLookupQueries pre v pres resolve)=some queues)
    (hr : ∀r∈rs,r.receiverId.length≤64) :
    ((accounts++queues++upsWalkInventory Is).flatMap (·.steps)).length≤
      132*rs.length+12+20*v.shards.length+4*pres.length+4*Is.length := by
  have hac:=native_account_query_rows pairs rs accounts ha hr
  have hqc:=native_queue_rows pairs pre v pres resolve queues hq
  simp only [List.flatMap_append,List.length_append,ups_inventory_rows,hqc]
  omega

theorem combined_lookup_log22 (pairs : List (PTrie×PTrie)) (rs : List Receipt)
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (accounts queues : List WalkR) (Is : List Render.UpsInst)
    (ha : nativeQueryWalks pairs (accountLookupQueries rs)=some accounts)
    (hq : nativeQueryWalks pairs (queueLookupQueries pre v pres resolve)=some queues)
    (hr : ∀r∈rs,r.receiverId.length≤64)
    (hn : rs.length≤4481) (hg : 24*v.shards.length≤2000000)
    (hk : pres.length≤32) (hu : Is.length≤32) :
    ((accounts++queues++upsWalkInventory Is).flatMap (·.steps)).length≤2258420 ∧
    ((accounts++queues++upsWalkInventory Is).flatMap (·.steps)).length+1≤2^22 := by
  have hh:=combined_lookup_rows pairs rs pre v pres resolve accounts queues Is ha hq hr
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
