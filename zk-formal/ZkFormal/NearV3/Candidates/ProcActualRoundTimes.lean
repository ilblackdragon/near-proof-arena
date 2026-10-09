import ZkFormal.NearV3.Candidates.ProcActualEntryTimes
namespace ZkFormal.NearV3.Candidates.ProcActualRoundTimes
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound

def rounds (s : Acc) : Array Gen.RoundD := s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

def Good (rd : Gen.RoundD) : Prop :=
  rd.entries.Pairwise (fun a b=>a.ts<b.ts) ∧ ∀e∈rd.entries,e.ts<rd.T

def AllGood (s : Acc) : Prop := ∀rd∈(rounds s).toList,Good rd

set_option maxHeartbeats 800000 in
theorem round_times (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : Acc) (hs : AllGood s) (hR : cv.size≤T0) (ht : cv.size≤rd.kstart)
    (hT : time s=T0+(rd.kstart-cv.size))
    (hb : rd.bucket.Pairwise (fun a b=>a.ts<b.ts) ∧ ∀b∈rd.bucket,b.ts<rd.kstart)
    (h : step I cv key rd s=.ok (.yield out)) : AllGood out := by
  have htranslated := ProcActualEntryTimes.translated_bucket cv.size (time s) rd.kstart rd.bucket hR ht hT hb.1 hb.2
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have he := ProcActualEntryTimes.batch_times I cv rd ?sh tm
      (sb,rb,aa,gg,ol,os,orr,ps,used,gi,#[]) ?next (by assumption)
    simp only [ProcActualEntryTimes.times,ProcActualEntryTransition.entries,
      Array.toList_empty,List.map_nil,List.nil_append] at he
    intro d hd
    simp only [rounds,Array.toList_push,List.mem_append,List.mem_singleton] at hd
    rcases hd with hd|rfl
    · exact hs d hd
    · constructor
      · apply List.pairwise_map.mp
        rw [he]
        exact htranslated.1
      · intro e hm
        have hmem : e.ts∈rd.bucket.map (fun b=>ProcPushSortContract.stampTime cv.size b.ts) := by
          rw [←he]
          exact List.mem_map_of_mem hm
        exact htranslated.2 e.ts hmem

theorem good_checks (rd : Gen.RoundD) (h : Good rd) :
    ∀i,i<rd.entries.length → check (rd.entries.toArray[i]!.ts <
      (if i+1=rd.entries.toArray.size then rd.T else rd.entries.toArray[i+1]!.ts))
      "bucket ts order"=.ok () :=
  fun i hi=>ProcActualEntryTimes.entry_compare rd.entries rd.T i h.1 h.2 hi
open ProcActualRoundTransition in
theorem trace_times (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (key : List Nat) (initial : PState) (start : Nat) (rs : List Round) (st : PState) (t : Nat)
    (ht : ProcModelBatchTrace.Trace I.ids.length I.allowed (ProcActualConversionExact.view cv)
      initial start rs st t)
    (hs : ProcActualAllowanceShape.Shape I.ids.length initial)
    (hv : ∀rd∈rs,∀v∈rd.shuffled,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hsize : ∀rd∈rs,1≤rd.bucket.length ∧ rd.bucket.length<16384)
    (htags : ∀rd∈rs,ProcActualBucketGuards.Tagged rd)
    (hR : cv.size≤T0)
    (htimes : ∀rd∈rs,rd.bucket.Pairwise (fun a b=>a.ts<b.ts) ∧ ∀b∈rd.bucket,b.ts<rd.kstart)
    (s : Acc) (hc : ProcActualReplayClock.Clock s) (hg : AllGood s) (ha : Aligned key cv s initial start) :
    ∃out,forIn rs s (step I cv key)=.ok out ∧ Aligned key cv out st t ∧ ProcActualReplayClock.Clock out ∧ AllGood out := by
  induction ht with
  | nil => exact ⟨s,rfl,ha,hc,hg⟩
  | @snoc rs st t ht rd st' t' hb ih =>
    obtain ⟨mid,hm,ham,hcm,hgm⟩ := ih (fun r hr=>hv r (by simp [hr]))
      (fun r hr=>hsize r (by simp [hr])) (fun r hr=>htags r (by simp [hr])) (fun r hr=>htimes r (by simp [hr]))
    have hmshape := trace_shape I.ids.length I.allowed (ProcActualConversionExact.view cv)
      initial start rs st t hs ht
    have hb' := hb
    rw [←ham.1,←ham.2] at hb'
    have hms : ProcActualAllowanceShape.Shape I.ids.length
        (ProcActualReplayEntry.state (entryAcc mid) (ZkFormal.Chacha.rngAt key (position mid))) := by
      rw [ham.1]; exact hmshape
    obtain ⟨out,ho,hao⟩ := round_transition I cv hcv key rd mid st' t' hms
      (hv rd (by simp)) (hsize rd (by simp)) (htags rd (by simp)) hb'
    have hstart : rd.kstart=t := by
      obtain ⟨rng,pending,result,h1,h2,h3,h4,h5,h6⟩ := hb
      exact h6
    have ht0 : cv.size≤rd.kstart := by rw [hstart,←ham.2]; omega
    have htime : time mid=T0+(rd.kstart-cv.size) := by
      rw [hstart,←ham.2]
      simpa [ProcActualReplayClock.Clock,Nat.add_sub_cancel_left] using hcm
    have hgo := round_times I cv key rd mid out hgm hR ht0 htime (htimes rd (by simp)) ho
    have hco := ProcActualReplayClock.round_clock I cv key rd mid out hcm ho
    refine ⟨out,?_,hao,hco,hgo⟩
    exact append_ok (step I cv key) (step_yields I cv key) rs [rd] s mid out hm
      (by simp only [List.forIn_cons,ho,bind,Except.bind,List.forIn_nil,pure,Except.pure])

open NearSpecV3.Scheduler ProcActualRoundTransition in
theorem prepared_times (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (s : Acc) (hclock : ProcActualReplayClock.Clock s) (hgood0 : AllGood s)
    (ha : Aligned (NearSpecV3.leWords sp.seed) cv s
      (ProcActualInput.initial (ProcPreparedSequence.input sp prev)) cv.size) :
    ∃out last,forIn rs s (step (ProcPreparedSequence.input sp prev) cv (NearSpecV3.leWords sp.seed))=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last ∧ ProcActualReplayClock.Clock out ∧ AllGood out := by
  let I := ProcPreparedSequence.input sp prev
  have hreq : convRaw I.p I.ids.length I.raw=ProcActualConversionExact.view cv := by
    simpa [ProcActualConversionExact.view] using
      (ProcActualConversionExact.loop_view I I.raw #[] cv hcv).symm
  have hlen : (convRaw I.p I.ids.length I.raw).length=cv.size := by
    rw [hreq]; simp [ProcActualConversionExact.view]
  obtain ⟨last,ht⟩ := ProcModelBatchTrace.process_trace I.ids.length I.allowed
    (convRaw I.p I.ids.length I.raw) (ProcActualInput.initial I) st _ rs hproc
  rw [hlen,hreq] at ht
  have hgood := ProcPreparedRequestGood.converted_good I.p I.ids.length I.raw hs.params
  have hv := ProcShufflePointers.process_pointers I.ids.length I.allowed
    (convRaw I.p I.ids.length I.raw) (fun q hq=>Nat.le_of_lt (hgood q hq).1) _ st _ rs hproc
  have htags := ProcActualBucketGuards.process_tags I.ids.length I.allowed _ _ st _ rs hproc
  have hb := ProcBucketSize.process_bounds I.ids.length I.allowed _ hgood _ st _ rs
    (ProcActualInput.prepared_ready sp hs prev) hproc
  have hraw := (ProcPreparedSequence.input_bounds sp prev hs).2.2
  change I.raw.length≤4096 at hraw
  have hc : (convRaw I.p I.ids.length I.raw).length≤I.raw.length := List.length_filterMap_le _ _
  have hsize : ∀rd∈rs,1≤rd.bucket.length ∧ rd.bucket.length<16384 := by
    intro rd hr
    have hh := hb rd hr
    omega
  rw [hreq] at hv
  have hconst : 4096≤T0 := by decide
  have hR : cv.size≤T0 := by omega
  have htimes := ProcModelTime.process_time I.ids.length I.allowed _ _ st _ rs hproc
  obtain ⟨out,ho,he,hco,hgo⟩ := trace_times I cv hcv (NearSpecV3.leWords sp.seed)
    (ProcActualInput.initial I) cv.size rs st last ht (ProcActualAllowanceShape.initial_shape I)
    (fun rd hr => (hv rd hr).2) hsize htags hR htimes s hclock hgood0 ha
  exact ⟨out,last,ho,he,hco,hgo⟩
theorem initial_good (I : Input) (cv : Array CReq) (ops : Array (Array Gen.MOp)) :
    AllGood (ProcActualReplayInitial.initial I cv ops) := by
  simp [AllGood,rounds,ProcActualReplayInitial.initial]

open NearSpecV3.Scheduler ProcActualRoundTransition ProcActualReplayFactor in
theorem replay_times (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs)) :
    ∃out last,replay (ProcPreparedSequence.input sp prev) cv rs=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last ∧
      ProcActualReplayClock.Clock out ∧ AllGood out := by
  let I := ProcPreparedSequence.input sp prev
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv
    (Array.replicate (I.ids.length*I.ids.length) #[])
  obtain ⟨out,last,hr,ha,hc,hg⟩ := prepared_times sp hs prev cv st rs hcv hproc
    (ProcActualReplayInitial.initial I cv ops) (ProcActualReplayClock.initial_clock I cv ops)
    (initial_good I cv ops) (ProcActualReplayInitial.initial_aligned I cv ops)
  refine ⟨out,last,?_,ha,hc,hg⟩
  change (forIn cv _ (readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords sp.seed)))=.ok out
  rw [hop]
  exact hr

open NearSpecV3.Scheduler in
theorem replay_good (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (out : Acc) (hr : ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok out) :
    AllGood out := by
  obtain ⟨actual,last,ha,_,_,hg⟩ := replay_times sp hs prev cv st rs hcv hproc
  have he := Except.ok.inj (ha.symm.trans hr)
  subst actual
  exact hg
end ZkFormal.NearV3.Candidates.ProcActualRoundTimes
