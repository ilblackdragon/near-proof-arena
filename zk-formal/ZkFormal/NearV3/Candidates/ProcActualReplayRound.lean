import ZkFormal.NearV3.Candidates.ProcActualEntryFactor
import ZkFormal.NearV3.Candidates.ProcActualBatchReplay
import ZkFormal.NearV3.Candidates.ProcActualBucketGuards
namespace ZkFormal.NearV3.Candidates.ProcActualReplayRound
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
abbrev Acc := ProcActualReplayChain.ReplayAcc

/-- Full actual outer-round body, retaining bucket collection and metadata. -/
def step (I : Input) (conv : Array CReq) (key : List Nat) (rd : Round)
    (acc : Acc) : Except String (ForInStep Acc) := do
  let (sb0,rb0,aa0,gg0,opsL0,opsS0,opsR0,pushes0,bucketsAll0,startT,kpos0,Kq0,zq0,used0,rounds0,gidx0) := acc
  let mut sb := sb0
  let mut rb := rb0
  let mut aa := aa0
  let mut gg := gg0
  let mut opsL := opsL0
  let mut opsS := opsS0
  let mut opsR := opsR0
  let mut pushes := pushes0
  let mut bucketsAll := bucketsAll0
  let mut T := startT
  let mut kpos := kpos0
  let mut Kq := Kq0
  let mut zq := zq0
  let mut used := used0
  let mut rounds := rounds0
  let mut gidx := gidx0
  let R := conv.size
  let tsOf (t : Nat) := if t<R then t else T0+(t-R)
  let L := rd.bucket.length
  check (L ≥ 1 && L < 16384) "bucket size"
  let vals := rd.bucket.map (·.v)
  let (sh, kend) ← replayShuffle key kpos vals
  check (sh == rd.shuffled) "shuffle replay differs"
  check (rd.steps.length == L) "steps ≠ bucket"
  for b in rd.bucket do
    check (b.key == rd.key && b.z == rd.z) "bucket push key/z"
    bucketsAll := bucketsAll.push (tsOf b.ts, b.key, b.z, b.v)
  let mut ents : Array Entry := #[]
  let (sbNext,rbNext,aaNext,ggNext,opsLNext,opsSNext,opsRNext,pushesNext,usedNext,gidxNext,entsNext) ← forIn (List.range L) (sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,ents) (ProcActualReplayEntry.step I conv rd sh T)
  sb := sbNext
  rb := rbNext
  aa := aaNext
  gg := ggNext
  opsL := opsLNext
  opsS := opsSNext
  opsR := opsRNext
  pushes := pushesNext
  used := usedNext
  gidx := gidxNext
  ents := entsNext
  rounds := rounds.push ⟨rd.key, rd.z, T, L, kpos, kend, Kq, zq, ents.toList⟩
  T := T + L
  kpos := kend
  Kq := rd.key
  zq := rd.z
  return .yield (sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,T,kpos,Kq,zq,used,rounds,gidx)
def entryAcc (s : Acc) : ProcActualReplayEntry.Acc :=
  let (sb,rb,aa,gg,opsL,opsS,opsR,pushes,_,_,_,_,_,used,_,gidx) := s
  (sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,#[])
def time (s : Acc) : Nat := s.2.2.2.2.2.2.2.2.2.1
def position (s : Acc) : Nat := s.2.2.2.2.2.2.2.2.2.2.1

theorem batch_count (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st st' : PState) (t t' : Nat) (rd : Round)
    (hb : ProcModelBatchTrace.Batch n allowed reqs st t rd st' t') :
    rd.steps.length=rd.bucket.length := by
  obtain ⟨rng,pending,out,hshuffle,hmodel,hsteps,_,_,_⟩ := hb
  have hc := (ProcModelEntryShape.entries_counts n allowed reqs rd.key rd.z rd.shuffled _ out hmodel).2
  have hl := (shuffle_perm hshuffle).length_eq
  rw [hsteps,hc]
  simpa using hl

/-- The actual round body succeeds from model batch execution and previously
proved bucket/pointer invariants; no entry-loop success premise is supplied. -/
theorem round_success (I : Input) (cv : Array CReq)
    (hcv : forIn I.raw #[] (ProcActualConverted.step I)=.ok cv)
    (key : List Nat) (rd : Round) (s : Acc) (st' : PState) (t' : Nat)
    (hs : ProcActualAllowanceShape.Shape I.ids.length
      (ProcActualReplayEntry.state (entryAcc s) (ZkFormal.Chacha.rngAt key (position s))))
    (hv : ∀v∈rd.shuffled,ProcRequestPointers.Valid (ProcActualConversionExact.view cv) v)
    (hsize : 1≤rd.bucket.length ∧ rd.bucket.length<16384)
    (htags : ProcActualBucketGuards.Tagged rd)
    (hb : ProcModelBatchTrace.Batch I.ids.length I.allowed (ProcActualConversionExact.view cv)
      (ProcActualReplayEntry.state (entryAcc s) (ZkFormal.Chacha.rngAt key (position s)))
      (cv.size+ProcActualEntryTransition.cursor (entryAcc s)) rd st' t') :
    ∃out,step I cv key rd s=.ok (.yield out) := by
  have hcount := batch_count _ _ _ _ _ _ _ _ hb
  obtain ⟨last,next,hshuffle,hentry,_,_,_,_,_⟩ :=
    ProcActualBatchReplay.batch_replay I cv hcv key (position s) (time s) (entryAcc s) rd st' t' hs hv hb
  rcases s with ⟨sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,T,kpos,Kq,zq,used,rounds,gidx⟩
  obtain ⟨collected,hcollect,_⟩ := ProcActualBucketGuards.collect_success cv.size rd.key rd.z rd.bucket bucketsAll htags
  dsimp only [position,time,entryAcc] at hshuffle hentry
  unfold step
  change ∃out : Acc,(do
    check (rd.bucket.length≥1 && rd.bucket.length<16384) "bucket size"
    let (sh,kend) ← replayShuffle key kpos (rd.bucket.map (fun b : Push=>b.v))
    check (sh==rd.shuffled) "shuffle replay differs"
    check (rd.steps.length==rd.bucket.length) "steps ≠ bucket"
    let collected ← forIn rd.bucket bucketsAll (ProcActualBucketGuards.collectStep cv.size rd.key rd.z)
    let result ← forIn (List.range rd.bucket.length)
      (sb,rb,aa,gg,opsL,opsS,opsR,pushes,used,gidx,#[])
      (ProcActualReplayEntry.step I cv rd sh T)
    pure (ForInStep.yield (result.1,result.2.1,result.2.2.1,result.2.2.2.1,
      result.2.2.2.2.1,result.2.2.2.2.2.1,result.2.2.2.2.2.2.1,result.2.2.2.2.2.2.2.1,
      collected,T+rd.bucket.length,kend,rd.key,rd.z,result.2.2.2.2.2.2.2.2.1,
      rounds.push ⟨rd.key,rd.z,T,rd.bucket.length,kpos,kend,Kq,zq,result.2.2.2.2.2.2.2.2.2.2.toList⟩,
      result.2.2.2.2.2.2.2.2.2.1)))=.ok (.yield out)
  simp only [hshuffle,hcount,hcollect,hentry,check,hsize.1,hsize.2,decide_true,
    Bool.and_true,BEq.rfl,ite_true,bind,Except.bind,pure,Except.pure]
  exact ⟨_,rfl⟩

end ZkFormal.NearV3.Candidates.ProcActualReplayRound
