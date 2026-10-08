import ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
namespace ZkFormal.NearV3.Candidates.ProcActualParameterGuard
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler ProcActualReplayRound

theorem bounds (p : Params) (n : Nat) (hp : Params.calculate Config.pv86 n=some p) :
    p.base<2^24 ∧ p.maxSingleGrant-p.base<2^24 := by
  obtain ⟨hb,hg⟩ := pv86_base_le hp
  constructor <;> omega

theorem check_ok (p : Params) (n : Nat) (hp : Params.calculate Config.pv86 n=some p) :
    check (p.base<2^24 && p.maxSingleGrant-p.base<2^24) "params ≥ 2^24"=.ok () := by
  obtain ⟨hb,hd⟩ := bounds p n hp
  simp [check,hb,hd,pure,Except.pure]

def result (I : Input) (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc)
    (gs : Array Gen.Seg) (cs : ProcActualMemoryScan.Cmps) : Run :=
  let n := I.ids.length
  let lp := linkPass n I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  let (_,_,_,_,_,_,_,_,_,_,kpos,_,_,used,rounds,_) := s
  { tau, n, base := I.p.base, D := I.p.maxSingleGrant-I.p.base, seed := I.seed,
    key := NearSpecV3.leWords I.seed, a2 := lp.a2, conv := cv.toList, used,
    rounds := rounds.toList, segs := gs.toList, cmps := cs.toList, kfin := kpos, fin := st }

theorem finish_eq (sp : SchedPub) (hs : SchedPubOk sp) (prev : NearSpec.Bandwidth.State)
    (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc)
    (gs : Array Gen.Seg) (cs : ProcActualMemoryScan.Cmps) :
    ProcActualComparisonFactor.finish (ProcPreparedSequence.input sp prev) tau cv st s gs cs =
      (do
        check (cs.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"
        pure (result (ProcPreparedSequence.input sp prev) tau cv st s gs cs)) := by
  unfold ProcActualComparisonFactor.finish
  dsimp only
  rw [check_ok (ProcPreparedSequence.input sp prev).p sp.ids.length hs.params]
  rfl

theorem finish_success (sp : SchedPub) (hs : SchedPubOk sp) (prev : NearSpec.Bandwidth.State)
    (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc)
    (gs : Array Gen.Seg) (cs : ProcActualMemoryScan.Cmps)
    (hc : (cs.all fun (x,y,_)=>x<2^29 && y<2^29)=true) :
    ProcActualComparisonFactor.finish (ProcPreparedSequence.input sp prev) tau cv st s gs cs =
      .ok (result (ProcPreparedSequence.input sp prev) tau cv st s gs cs) := by
  rw [finish_eq sp hs]
  simp only [hc,check,ite_true,bind,Except.bind,pure,Except.pure]
theorem suffix_reduction (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (hk : ∀s,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s →
      ∀rd∈(ProcActualRoundTimes.rounds s).toList,rd.K≠0 → rd.K<rd.Kq) :
    ∃s gs cs,ProcActualReplayFactor.replay (ProcPreparedSequence.input sp prev) cv rs=.ok s ∧
      ProcActualRoundFactor.runRestRounds (ProcPreparedSequence.input sp prev) tau cv st rs =
      (do
        check (cs.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"
        pure (result (ProcPreparedSequence.input sp prev) tau cv st s gs cs)) := by
  obtain ⟨s,gs,cs,hr,he⟩ := ProcActualComparisonFactor.suffix_reduction sp hs prev tau cv st rs hcv hproc hk
  exact ⟨s,gs,cs,hr,he.trans (finish_eq sp hs prev tau cv st s gs cs)⟩
end ZkFormal.NearV3.Candidates.ProcActualParameterGuard
