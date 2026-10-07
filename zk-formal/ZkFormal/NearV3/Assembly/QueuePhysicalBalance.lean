import ZkFormal.NearV3.Assembly.QueueGlobalBalance

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen

/-- Physical QVC balance of the actual rank-resolved queue trace. The local
 parser validity and fit inputs are provided by the accepted-input constructor. -/
theorem plan_physical_qvc_balance {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    (log : Nat) (pub : List Fp)
    (hv : ∀ r ∈ queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)), r.Valid)
    (hfit : ((plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)).flatMap Walk.rows).length+
      recordsSize (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)))≤2^log) :
    let ws := plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub ValueTable.B_QVC true)).Perm
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub ValueTable.B_QVC false)) := by
  dsimp only
  have hs := mixedTrace_counter_messages _ _ hv log pub true hfit
  have hr := mixedTrace_counter_messages _ _ hv log pub false hfit
  have hl := (plan_qvc_balance pres hh).map Msg.toFp
  have hlogical :
      (((plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)).flatMap
          (fun w => w.counterWordMessages true) ++
        (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))).map
          (fun r => [r.vid,r.tau,r.mode,0])).map Msg.toFp).Perm
      (((plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0)).flatMap
          (fun w => w.counterWordMessages false) ++
        (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))).map
          (fun r => [r.vid,r.tau,r.mode,r.users])).map Msg.toFp) := by
    simpa only [queueRecords,List.map_map,Function.comp_def,queueCounterMsg,queueRecord] using hl
  exact hs.trans (hlogical.trans hr.symm)

end ZkFormal.NearV3.Assembly
