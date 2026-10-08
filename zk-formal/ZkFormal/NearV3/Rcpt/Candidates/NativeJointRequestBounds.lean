import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryBounds
import ZkFormal.NearV3.Rcpt.Candidates.SharedPhysicalBitmapBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly ZkFormal.Near

/-- The same executable receiver, refund, and queue inventory leaves room for
all accepted UPS slots; neither zero-valued reads nor refund queries are dropped. -/
theorem native_joint_request_bounds (pairs : List (PTrie×PTrie)) (rs : List Receipt)
    (pre : PTrie) (v : Qv.MainValues) (pres : List PTrie)
    (resolve : Qv.Candidates.CombinedWalkGen.Resolve) (ws : List WalkR) (Is : List Render.UpsInst)
    (hq : nativeQueryWalks pairs (allLookupQueries rs pre v pres resolve)=some ws)
    (hr : ∀r∈rs,r.wf=true) (hn : rs.length≤4481) (hg : 24*v.shards.length≤2000000)
    (hk : pres.length≤32) (hu : Is.length≤32) :
    ((ws++upsWalkInventory Is).flatMap (·.steps)).length≤3441404 := by
  have hw:=nativeQueryWalks_rows pairs _ ws hq
  have hq:=allLookupQueries_rows rs pre v pres resolve hr hn hg hk
  simp only [List.flatMap_append,List.length_append,ups_inventory_rows]
  omega

theorem native_joint_counter_ranges (pairs : List (PTrie×PTrie)) (rs : List Receipt)
    (pre : PTrie) (v : Qv.MainValues) (pres : List PTrie)
    (resolve : Qv.Candidates.CombinedWalkGen.Resolve) (ws : List WalkR) (Is : List Render.UpsInst)
    (hq : nativeQueryWalks pairs (allLookupQueries rs pre v pres resolve)=some ws)
    (hr : ∀r∈rs,r.wf=true) (hn : rs.length≤4481) (hg : 24*v.shards.length≤2000000)
    (hk : pres.length≤32) (hu : Is.length≤32) :
    (walkEdgeKeys (ws++upsWalkInventory Is)).length<Algebra.P ∧
    (walkBmapKeys (ws++upsWalkInventory Is)).length<Algebra.P := by
  have h:=native_joint_request_bounds pairs rs pre v pres resolve ws Is hq hr hn hg hk hu
  have he:=List.length_filterMap_le (fun st : WStep3=>if st.mode≤1 then some st.e else none) ((ws++upsWalkInventory Is).flatMap (·.steps))
  have hb:=List.length_filterMap_le (fun st : WStep3=>if st.mode=2 then some [st.e.getD 0 0,st.bm,st.hv] else none) ((ws++upsWalkInventory Is).flatMap (·.steps))
  unfold walkEdgeKeys walkBmapKeys
  change _<2013265921 ∧ _<2013265921
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
