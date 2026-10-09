import ZkFormal.NearV3.Candidates.ProcBatchSuccess
import ZkFormal.NearV3.Candidates.ProcPreparedLinks
namespace ZkFormal.NearV3.Candidates.ProcInitialLinks
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcPendingCurrent

theorem range_links (reqs : List Req) :
    (List.range reqs.length).map (fun i=>link reqs (i*64))=reqs.map (·.link) := by
  have hh := congrArg (List.map Req.link) (map_getD_range reqs default)
  simpa [List.map_map,Function.comp_def,link,List.getD_eq_getElem?_getD] using hh

theorem initial_nodup (reqs : List Req) (st : PState) (hn : (reqs.map (·.link)).Nodup) :
    ((ProcModelStep.initial reqs st).1.map (fun p=>link reqs p.v)).Nodup := by
  have hh : ((List.range reqs.length).map (fun i=>link reqs (i*64))).Nodup := by
    rw [range_links]; exact hn
  change List.Pairwise _ _ at hh ⊢
  rw [List.pairwise_map] at hh ⊢
  apply List.pairwise_filterMap.mpr
  apply hh.imp
  intro i j hij p hp q hq
  dsimp only at hp hq
  split at hp
  · contradiction
  · cases hp
    split at hq
    · contradiction
    · cases hq; exact hij

theorem prepared_initial_nodup (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) :
    let I := ProcPreparedSequence.input sp prev
    let reqs := convRaw I.p I.ids.length I.raw
    let st := ProcCoreReplay.initial I
    ((ProcModelStep.initial reqs st).1.map (fun p=>link reqs p.v)).Nodup :=
  initial_nodup _ _ (ProcPreparedLinks.prepared_links_nodup sp hs)
end ZkFormal.NearV3.Candidates.ProcInitialLinks
