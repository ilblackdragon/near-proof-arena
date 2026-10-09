import ZkFormal.NearV3.Candidates.ProcNativeLoopExistence
namespace ZkFormal.NearV3.Candidates.ProcNativeInitial
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcNativeGrant ProcNativePush

private theorem filter_congr {α β : Type} (xs : List α) (f g : α→Option β)
    (h : ∀x∈xs,f x=g x) : xs.filterMap f=xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons,h x (by simp)]
    rw [ih (fun y hy=>h y (by simp [hy]))]

theorem conv_nonempty (p : Params) (n : Nat) (raw : List RawReq) :
    ∀q∈convRaw p n raw,q.incs≠[] := by
  intro q hq
  obtain ⟨r,hr,hq⟩ := List.mem_filterMap.mp hq
  cases hi : incsOf p r.bm with
  | nil => simp [hi] at hq
  | cons x xs => simp only [hi,Option.some.injEq] at hq; subst q; simp

theorem initial_pushes (reqs : List Req) (st : PState) (hr : ∀q∈reqs,q.incs≠[]) :
    (ProcModelStep.initial reqs st).1.map toPM=initPushes reqs (native st) := by
  unfold ProcModelStep.initial initPushes
  rw [List.map_filterMap,←List.filterMap_eq_map']
  apply filter_congr
  intro i hi
  have hib : i<reqs.length := List.mem_range.mp hi
  have hm : reqs.toArray[i]!∈reqs := by
    rw [getElem!_pos reqs.toArray i (by simpa using hib)]
    exact List.mem_iff_getElem.mpr ⟨i,hib,by simp⟩
  have he : reqs.toArray[i]!.incs.isEmpty=false := by simpa using hr _ hm
  simp only [he,Bool.false_eq_true,ite_false,Option.map_some,toPM,native,zNext]
  simp [List.getD_eq_getElem?_getD,hib]

theorem initial_buckets (reqs : List Req) (st : PState) (hr : ∀q∈reqs,q.incs≠[]) :
    reqs.foldl (fun bk q=>bucketPush (native st).allowance[q.link]! q bk) []=
      bucketsOf reqs ((ProcModelStep.initial reqs st).1.map toPM) := by
  rw [initial_pushes reqs st hr]
  exact init_buckets reqs (native st)

/-- A successful actual native process produces a successful complete event
model with the same resulting state. No model-success premise remains. -/
theorem prepared_process_exists (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length) (prev : NearSpec.Bandwidth.State)
    (stF : St)
    (h : processRequests sp.ids.length sp.allowed
      (native (ProcCoreReplay.initial (ProcPreparedSequence.input sp prev)))
      (convRaw sp.params sp.ids.length (instOf sp).raw)=some stF) :
    ∃st rs,ProcCoreReplay.process (ProcPreparedSequence.input sp prev)=.ok (st,rs) ∧ native st=stF := by
  let I := ProcPreparedSequence.input sp prev
  let reqs := convRaw I.p I.ids.length I.raw
  let st := ProcCoreReplay.initial I
  let s := ProcModelStep.initial reqs st
  have hM : I.p.maxShardBandwidth≤u64Max := by
    change sp.params.maxShardBandwidth≤u64Max
    rw [pv86_maxShard hs.params]
    decide
  have hg := ProcNativeGrant.initial_inv I hs.n1 hs.params ha
  have ht : ProcModelTime.Inv s := ⟨ProcPendingTime.initial reqs st,by simp [s,ProcModelStep.initial]⟩
  change processLoop I.ids.length I.allowed (1+(reqs.map (fun q : Req=>q.incs.length)).sum) (native st)
    (reqs.foldl (fun bk q=>bucketPush (native st).allowance[q.link]! q bk) [])=some stF at h
  rw [initial_buckets reqs st (conv_nonempty _ _ _)] at h
  obtain ⟨out,ho,hend,hfinal⟩ := ProcNativeLoopExistence.loop_exists I.ids.length I.p.maxShardBandwidth hM
    I.allowed reqs (ProcPreparedRequestGood.converted_good _ _ _ hs.params) _ 0 s
    (ProcRoundSuccess.initial_ready sp hs prev) ht hg stF h
  refine ⟨out.2.1,out.2.2.2.1,?_,hfinal⟩
  unfold ProcCoreReplay.process
  rw [ProcModelStep.process_eq,List.range_eq_range']
  change (do
    let result ← forIn (List.range' 0 (1+(reqs.map (fun q : Req=>q.incs.length)).sum)) s (ProcModelStep.step I.ids.length I.allowed reqs)
    if !result.1.isEmpty then throw "out of fuel"
    return (result.2.1,result.2.2.2.1))=.ok _
  simp only [ho,bind,Except.bind,hend,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,
    ite_false,pure,Except.pure]
end ZkFormal.NearV3.Candidates.ProcNativeInitial
