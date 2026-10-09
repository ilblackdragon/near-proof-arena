import ZkFormal.NearV3.Candidates.ProcActualReplayInitial
import ZkFormal.NearV3.Candidates.ProcActualReplayBoundaryGuards
namespace ZkFormal.NearV3.Candidates.ProcActualFinalStateGuards
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open NearSpecV3.Scheduler ProcActualReplayRound ProcActualRoundTransition

/-- Exact two final equality checks from the generator suffix. -/
def checks (s : Acc) (st : PState) : Except String Unit := do
  let (sb,rb,aa,gg,_,_,_,_,_,_,kpos,_,_,_,_,_) := s
  check (sb == st.sb && rb == st.rb && aa == st.al && gg == st.g) "final state differs"
  check (kpos == rngPos st.rng) "final RNG position differs"

theorem aligned_checks (key : List Nat) (cv : Array CReq) (s : Acc) (st : PState) (t : Nat)
    (h : Aligned key cv s st t) : checks s st=.ok () := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  have he := h.1
  change ({sb:=sb,rb:=rb,al:=aa,g:=gg,rng:=ZkFormal.Chacha.rngAt key kp} : PState)=st at he
  subst st
  simp [checks,ProcActualReplayBoundaryGuards.rngAt_position,Gen.check,
    bind,Except.bind,pure,Except.pure]

theorem initialized_checks (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (cv : Array CReq) (st : PState) (rs : List Round)
    (hcv : forIn (ProcPreparedSequence.input sp prev).raw #[]
      (ProcActualConverted.step (ProcPreparedSequence.input sp prev))=.ok cv)
    (hproc : ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs))
    (opsL : Array (Array Gen.MOp)) :
    ∃out last,forIn rs (ProcActualReplayInitial.initial (ProcPreparedSequence.input sp prev) cv opsL)
      (step (ProcPreparedSequence.input sp prev) cv (NearSpecV3.leWords sp.seed))=.ok out ∧
      Aligned (NearSpecV3.leWords sp.seed) cv out st last ∧ checks out st=.ok () := by
  obtain ⟨out,last,ho,ha⟩ := ProcActualReplayInitial.initialized_replay sp hs prev cv st rs hcv hproc opsL
  exact ⟨out,last,ho,ha,aligned_checks _ _ _ _ _ ha⟩
end ZkFormal.NearV3.Candidates.ProcActualFinalStateGuards
