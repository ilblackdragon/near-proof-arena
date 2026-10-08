import ZkFormal.NearV3.Candidates.ProcNativeInitial
namespace ZkFormal.NearV3.Candidates.ProcActualInput
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler ProcNativeGrant

/-- Exact native lookup: unknown IDs are ignored and later entries overwrite.
The original previous state and its serialized bytes are never normalized. -/
def allowStep (ids : List Nat) (a : Array Nat) (la : NearSpec.Bandwidth.LinkAllowance) : Array Nat :=
  match indexOf ids la.sender,indexOf ids la.receiver with
  | some s,some r=>a.set! (s*ids.length+r) la.allowance
  | _,_=>a

def allowances (ids : List Nat) (prev : NearSpec.Bandwidth.State) : Array Nat :=
  prev.links.foldl (allowStep ids) (Array.replicate (ids.length*ids.length) 0)

def initial (I : Input) : PState :=
  let lp := linkPass I.ids.length I.p I.allowed (allowances I.ids I.prev)
  ⟨lp.sb,lp.rb,lp.a2,lp.g2,NearSpecV3.Rng.ofSeed I.seed⟩

def process (I : Input) : Except String (PState×List Round) :=
  let reqs := convRaw I.p I.ids.length I.raw
  processEv I.ids.length I.allowed reqs (initial I) (1+(reqs.map (·.incs.length)).sum)

theorem step_size (ids : List Nat) (a : Array Nat) (la : NearSpec.Bandwidth.LinkAllowance) :
    (allowStep ids a la).size=a.size := by
  unfold allowStep
  split <;> simp

theorem fold_size (ids : List Nat) (ls : List NearSpec.Bandwidth.LinkAllowance) (a : Array Nat) :
    (ls.foldl (allowStep ids) a).size=a.size := by
  induction ls generalizing a with
  | nil => rfl
  | cons l ls ih => simpa only [List.foldl_cons,step_size] using ih (allowStep ids a l)

theorem allowances_size (ids : List Nat) (prev : NearSpec.Bandwidth.State) :
    (allowances ids prev).size=ids.length*ids.length := by simp [allowances,fold_size]

theorem initial_native (I : Input) (hn : 1≤I.ids.length)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (ha : I.allowed.size=I.ids.length*I.ids.length) :
    (List.range (I.ids.length*I.ids.length)).foldl (fun st l=>(tryGrant I.ids.length I.allowed st l I.p.base).2)
      ({senderBudget:=Array.replicate I.ids.length I.p.maxShardBandwidth,
        receiverBudget:=Array.replicate I.ids.length I.p.maxShardBandwidth,
        allowance:=(allowances I.ids I.prev).map (fun a=>min (min (a+I.p.maxShardBandwidth/I.ids.length) u64Max) I.p.maxAllowance),
        granted:=Array.replicate (I.ids.length*I.ids.length) 0,rng:=NearSpecV3.Rng.ofSeed I.seed} : St)=
      native (initial I) :=
  linkPass_eq hn hp I.allowed (allowances I.ids I.prev) ha (allowances_size _ _) _

theorem initial_inv (I : Input) (hn : 1≤I.ids.length)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (ha : I.allowed.size=I.ids.length*I.ids.length) : Inv I.ids.length I.p.maxShardBandwidth (initial I) := by
  have hM : I.p.maxShardBandwidth≤u64Max := by rw [pv86_maxShard hp]; decide
  have h0 : GInv I.ids.length I.p.maxShardBandwidth
      ({senderBudget:=Array.replicate I.ids.length I.p.maxShardBandwidth,
        receiverBudget:=Array.replicate I.ids.length I.p.maxShardBandwidth,
        allowance:=(allowances I.ids I.prev).map (fun a=>min (min (a+I.p.maxShardBandwidth/I.ids.length) u64Max) I.p.maxAllowance),
        granted:=Array.replicate (I.ids.length*I.ids.length) 0,rng:=NearSpecV3.Rng.ofSeed I.seed} : St) := by
    intro l
    have hg := getElem!_replicate_le (I.ids.length*I.ids.length) 0 l
    have hb := getElem!_replicate_le I.ids.length I.p.maxShardBandwidth (l/I.ids.length)
    change (Array.replicate _ 0)[l]!+(Array.replicate _ I.p.maxShardBandwidth)[l/I.ids.length]!≤I.p.maxShardBandwidth
    omega
  have hh := baseFold_ginv hM I.allowed I.p.base (List.range (I.ids.length*I.ids.length)) h0
  rw [initial_native I hn hp ha] at hh
  exact hh

theorem prepared_ready (sp : SchedPub) (hs : SchedPubOk sp) (prev : NearSpec.Bandwidth.State) :
    let I := ProcPreparedSequence.input sp prev
    let reqs := convRaw I.p I.ids.length I.raw
    ProcRoundSuccess.Ready reqs (ProcModelStep.initial reqs (initial I)) := by
  let I := ProcPreparedSequence.input sp prev
  let reqs := convRaw I.p I.ids.length I.raw
  refine ⟨ProcPendingCurrent.initial_current reqs (initial I) ?_,
    ProcInitialLinks.initial_nodup reqs (initial I) (ProcPreparedLinks.prepared_links_nodup sp hs),
    ProcRequestPointers.initial_valid _ _,ProcRoundGuards.initial _ _⟩
  intro q hq
  have hb := ProcPreparedLinks.prepared_links_bound sp q hq
  simpa [initial,linkPass,I,ProcPreparedSequence.input] using hb

theorem prepared_process_exists (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length) (prev : NearSpec.Bandwidth.State)
    (stF : St)
    (h : processRequests sp.ids.length sp.allowed
      (native (initial (ProcPreparedSequence.input sp prev)))
      (convRaw sp.params sp.ids.length (instOf sp).raw)=some stF) :
    ∃st rs,process (ProcPreparedSequence.input sp prev)=.ok (st,rs) ∧ native st=stF := by
  let I := ProcPreparedSequence.input sp prev
  let reqs := convRaw I.p I.ids.length I.raw
  let s := ProcModelStep.initial reqs (initial I)
  have hM : I.p.maxShardBandwidth≤u64Max := by
    change sp.params.maxShardBandwidth≤u64Max
    rw [pv86_maxShard hs.params]
    decide
  have ht : ProcModelTime.Inv s := ⟨ProcPendingTime.initial reqs (initial I),by simp [s,ProcModelStep.initial]⟩
  change processLoop I.ids.length I.allowed (1+(reqs.map (·.incs.length)).sum) (native (initial I))
    (reqs.foldl (fun bk q=>bucketPush (native (initial I)).allowance[q.link]! q bk) [])=some stF at h
  rw [ProcNativeInitial.initial_buckets reqs (initial I) (ProcNativeInitial.conv_nonempty _ _ _)] at h
  obtain ⟨out,ho,hend,hfinal⟩ := ProcNativeLoopExistence.loop_exists I.ids.length I.p.maxShardBandwidth hM
    I.allowed reqs (ProcPreparedRequestGood.converted_good _ _ _ hs.params) _ 0 s
    (prepared_ready sp hs prev) ht (initial_inv I hs.n1 hs.params ha) stF h
  refine ⟨out.2.1,out.2.2.2.1,?_,hfinal⟩
  unfold process
  rw [ProcModelStep.process_eq,List.range_eq_range']
  change (do
    let result ← forIn (List.range' 0 (1+(reqs.map (fun q : Req=>q.incs.length)).sum)) s
      (ProcModelStep.step I.ids.length I.allowed reqs)
    if !result.1.isEmpty then throw "out of fuel"
    return (result.2.1,result.2.2.2.1))=.ok _
  simp only [ho,bind,Except.bind,hend,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,
    ite_false,pure,Except.pure]
end ZkFormal.NearV3.Candidates.ProcActualInput
