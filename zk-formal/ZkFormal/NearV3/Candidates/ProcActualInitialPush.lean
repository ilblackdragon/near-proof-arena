import ZkFormal.NearV3.Candidates.ProcActualTracePush
namespace ZkFormal.NearV3.Candidates.ProcActualInitialPush
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Facts (I : Input) (cv : Array CReq) : Prop := ∀i, i<cv.size →
  cv[i]!.cid=i ∧ cv[i]!.key=(ProcActualInput.initial I).al[cv[i]!.link]! ∧ cv[i]!.incs≠[]

theorem step_facts (I : Input) (q : RawReq) (cv : Array CReq) (hs : Facts I cv)
    (out : ForInStep (Array CReq)) (h : ProcActualConverted.step I q cv=.ok out) :
    ExceptLoop.StepInv (Facts I) out := by
  unfold ProcActualConverted.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | change Facts I (cv.push _)
      intro i hi
      by_cases hi' : i<cv.size
      · simpa [getElem!_pos,Array.size_push,Nat.lt_succ_of_lt hi',hi',Array.getElem_push_lt] using hs i hi'
      · have he : i=cv.size := by simp only [Array.size_push] at hi; omega
        subst i
        simp only [getElem!_pos,Array.size_push,Nat.lt_succ_self,Array.getElem_push_eq]
        refine ⟨trivial,rfl,?_⟩
        intro hn
        have hl := congrArg List.length hn
        simp only [incsOf,incsFrom_length,List.length_nil] at hl
        have hb : (setBits q.bm).isEmpty=false := by simpa using (show ¬(setBits q.bm).isEmpty=true from by assumption)
        have : setBits q.bm=[] := List.length_eq_zero_iff.mp hl
        simp [this] at hb

theorem loop_facts (I : Input) (cv : Array CReq)
    (h : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv) : Facts I cv :=
  ExceptLoop.invariant I.raw (ProcActualConverted.step I) (Facts I)
    (fun q _ cv hs out ho=>step_facts I q cv hs out ho) #[] cv (by simp [Facts]) h
private theorem filter_congr {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀x∈xs,f x=g x) : xs.filterMap f=xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons,h x (by simp),ih (fun x hx=>h x (by simp [hx]))]

theorem initial_records (I : Input) (cv : Array CReq) (hf : Facts I cv) :
    (ProcModelStep.initial (ProcActualConversionExact.view cv) (ProcActualInput.initial I)).1=
      cv.toList.map (fun c=>(⟨c.cid,c.key,if c.key=0 then 1 else 0,c.cid*64⟩ : Push)) := by
  have hi := ProcActualEntryTransition.map_indices cv.toList
  simp only [Array.length_toList] at hi
  conv => rhs; rw [←hi,List.map_map]
  dsimp only [ProcModelStep.initial,ProcActualConversionExact.view]
  simp only [List.length_map,Array.length_toList]
  conv => rhs; rw [←List.filterMap_eq_map']
  apply filter_congr
  intro i hi
  have hb := List.mem_range.mp hi
  obtain ⟨hid,hkey,hne⟩ := hf i hb
  have hq : (cv.toList.map (fun c=>({link:=c.link,incs:=c.incs} : NearSpecV3.Scheduler.Req))).toArray[i]! =
      ({link:=cv[i]!.link,incs:=cv[i]!.incs} : NearSpecV3.Scheduler.Req) := by
    simp [hb]
  rw [hq]
  simp only [getElem!_def] at hid hkey hne ⊢
  simp [hne,hid,hkey]

theorem initial_stamped (I : Input) (cv : Array CReq)
    (h : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv) :
    ((ProcModelStep.initial (convRaw I.p I.ids.length I.raw) (ProcActualInput.initial I)).1.map
      (ProcPushConservation.stamp cv.size))=
      cv.toList.map (fun c=>(c.cid,c.key,if c.key=0 then 1 else 0,c.cid*64)) := by
  have hf := loop_facts I cv h
  have hv : convRaw I.p I.ids.length I.raw=ProcActualConversionExact.view cv := by
    simpa [ProcActualConversionExact.view] using
      (ProcActualConversionExact.loop_view I I.raw #[] cv h).symm
  rw [hv,initial_records I cv hf,List.map_map]
  apply List.map_congr_left
  intro c hc
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hc
  have hb : i<cv.size := by simpa using hi
  have he' : cv[i]! =c := by simpa [getElem!_pos,hb] using he
  have hid := (hf i hb).1
  rw [he'] at hid
  simp [ProcPushConservation.stamp,hid,hb]

open NearSpecV3.Scheduler in
theorem replay_conservation (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out ∧
      (ProcActualGeneratedPush.pushes (ProcActualReplayRound.entryAcc out)).toList.Perm
        (ProcActualPoppedLog.buckets out).toList := by
  obtain ⟨out,last,hr,ha,hclock,hpush,hpop⟩ :=
    ProcActualTracePush.replay_push sp hs prev cv st rs hcv hproc
  refine ⟨out,hr,?_⟩
  have hh := ProcActualPoppedLog.process_conservation (ProcPreparedSequence.input sp prev) cv st rs hproc out hr
  rw [List.map_append,initial_stamped _ cv hcv] at hh
  rw [hpush]
  exact hh

end ZkFormal.NearV3.Candidates.ProcActualInitialPush
