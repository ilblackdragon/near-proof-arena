import ZkFormal.NearV3.Candidates.NativeQueueCounters
import ZkFormal.NearV3.Candidates.NativeQueryFinal

namespace ZkFormal.NearV3.Candidates.NativeQueueFinalMessages
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates.CombinedWalkGen

theorem planned_result (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (pairs : List (PTrie×PTrie)) (hp : pairs.map Prod.fst=pre::pres)
    (w : Walk) (hw : w∈plan pre v pres (NativeQueueIds.resolve pre v pres))
    (hh : ∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1) :
    NativeQueryFinal.result pairs (queueLookupQuery v.shards w)=
      if w.value.isSome then some w.vid else none := by
  obtain ⟨tree,rs,ht,hr,he⟩ := NativeQueueIds.plan_value pre v pres w hw hh
  have htree : (pre::pres)[w.tau]?=some tree := by
    have h := congrArg (fun xs=>xs[w.tau]?) (queueInputs_pre pre v pres)
    simpa only [List.getElem?_map,ht,Option.map_some] using h.symm
  have hpair : (pairs[w.tau]?).map Prod.fst=some tree := by
    rw [←List.getElem?_map,hp]
    exact htree
  cases hx : pairs[w.tau]? with
  | none=>simp [hx] at hpair
  | some pair=>
    have hfirst : pair.1=tree := by simpa [hx] using hpair
    simp only [NativeQueryFinal.result,queueLookupQuery,hx,Option.map_some,Option.getD_some,hfirst]
    have hoff : (pairs.take w.tau).map Prod.fst=(pre::pres).take w.tau := by rw [List.map_take,hp]
    simpa only [hoff,forestLookupVid] using he

theorem final_message (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (pairs : List (PTrie×PTrie)) (hp : pairs.map Prod.fst=pre::pres)
    (w : Walk) (hw : w∈plan pre v pres (NativeQueueIds.resolve pre v pres))
    (hh : ∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1) :
    w.finalWordMessages=[NativeQueryFinal.queryMessage pairs (queueLookupQuery v.shards w)] := by
  rw [NativeQueryFinal.queryMessage,planned_result pre v pres pairs hp w hw hh]
  cases hv:w.value.isSome <;>
    simp [Walk.finalWordMessages,NativeQueryFinal.message,queueLookupQuery,walkId,hv,FK_VAL,FK_ABS]

theorem plan_messages (pre : PTrie) (v : MainValues) (pres : List PTrie)
    (pairs : List (PTrie×PTrie)) (hp : pairs.map Prod.fst=pre::pres)
    (hh : ∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1) :
    (plan pre v pres (NativeQueueIds.resolve pre v pres)).flatMap Walk.finalWordMessages=
      (queueLookupQueries pre v pres (NativeQueueIds.resolve pre v pres)).map
        (NativeQueryFinal.queryMessage pairs) := by
  simp only [queueLookupQueries,List.map_map]
  rw [List.map_eq_flatMap]
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro w hw
  exact final_message pre v pres pairs hp w hw hh

open Qv.Candidates ZkFormal.Air ZkFormal.Algebra

theorem physical_messages {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (pairs : List (PTrie×PTrie)) (hp : pairs.map Prod.fst=pre::pres)
    (hh : ∀x∈queueInputs pre v pres,∀r∈x.2,r.Holds x.1)
    (vs : List ValueGen.Record) (hr : ∀r∈vs,r.Valid) (log : Nat) (pub : List Fp)
    (hfit : ((plan pre v pres (NativeQueueIds.resolve pre v pres)).flatMap Walk.rows).length+
      ValueGen.recordsSize vs≤2^log) :
    ((List.range (2^log)).flatMap (fun r=>rowTraffic CombinedTable.interactions
      (mixedTrace (plan pre v pres (NativeQueueIds.resolve pre v pres)) vs log) 0 r pub B_FINAL false)).Perm
    ((queueLookupQueries pre v pres (NativeQueueIds.resolve pre v pres)).map
      (NativeQueryFinal.queryMessage pairs) |>.map Msg.toFp) := by
  have hs := mixedTrace_all_messages _ vs hr
    (plan_group_slot pre v pres (NativeQueueIds.resolve pre v pres)) log pub B_FINAL false hfit
  simp only [mixedTraffic,Walk.wordMessages,ValueGen.canonicalTraffic,
    show B_FINAL≠ValueTable.B_QVC by decide,show B_FINAL≠B_QSH by decide,
    ite_true,ite_false,Bool.false_eq_true] at hs
  simp only [List.append_nil] at hs
  rw [plan_messages pre v pres pairs hp hh] at hs
  exact hs

end ZkFormal.NearV3.Candidates.NativeQueueFinalMessages
