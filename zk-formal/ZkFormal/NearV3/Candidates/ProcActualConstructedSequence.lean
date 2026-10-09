import ZkFormal.NearV3.Candidates.ProcActualPreparedGenerator
import ZkFormal.NearV3.Candidates.ProcActualPreparedSequence
namespace ZkFormal.NearV3.Candidates.ProcActualConstructedSequence
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open NearSpecV3.Scheduler

theorem inputs_success (is : List Input) (tau : Nat)
    (h : ∀I∈is,∀t,∃r,ActualRun.run I t=.ok r) :
    ∃rs,ProcActualNativeSequence.runInputs is tau=.ok rs := by
  induction is generalizing tau with
  | nil => exact ⟨[],rfl⟩
  | cons I is ih =>
    obtain ⟨r,hr⟩ := h I (by simp) tau
    obtain ⟨rs,hs⟩ := ih (tau+1) (fun J hJ=>h J (by simp [hJ]))
    exact ⟨r::rs,by simp only [ProcActualNativeSequence.runInputs,hr,hs,bind,Except.bind,pure,Except.pure]⟩

theorem prepared_constructed
    (ps : List (SchedPub × NearSpec.Bandwidth.State))
    (hc : ps.length≤33) (hp : ∀p∈ps,SchedPubOk p.1)
    (hr : ∀p∈ps,∀tau,∃r,ActualRun.run (ProcPreparedSequence.input p.1 p.2) tau=.ok r) :
    ∃rs,ProcActualNativeSequence.runInputs (ProcPreparedSequence.inputs ps) 0=.ok rs ∧
      ∀t pub,TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub := by
  obtain ⟨rs,hs⟩ := inputs_success (ProcPreparedSequence.inputs ps) 0 (by
    intro I hI tau
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hI
    exact hr p hp' tau)
  exact ⟨rs,hs,fun t pub=>ProcActualPreparedSequence.prepared_local ps rs hc hp hs t pub⟩

structure Call where
  sp : SchedPub
  ctx : NearSpecV3.ApplyCtx
  oldBytes : Option NearSpec.Bytes
  out : Output

def Accepted (p : NearSpecV3.Prep) (c : Call) : Prop :=
  c.sp∈p.sched ∧ NearSpecV3.schedPub c.ctx=some c.sp ∧ runCore c.sp c.oldBytes=some c.out

def Decoded (c : Call) (p : SchedPub × NearSpec.Bandwidth.State) : Prop :=
  p.1=c.sp ∧ ProcActualCore.decodePrevious c.oldBytes=some p.2

inductive DecodedList : List Call → List (SchedPub × NearSpec.Bandwidth.State) → Prop
  | nil : DecodedList [] []
  | cons {c cs q qs} : Decoded c q → DecodedList cs qs → DecodedList (c::cs) (q::qs)

theorem decoded_length {cs : List Call} {ps : List (SchedPub × NearSpec.Bandwidth.State)}
    (h : DecodedList cs ps) : cs.length=ps.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

open NearSpec NearSpecV3 in
theorem native_inputs {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (cs : List Call) (hc : ∀c∈cs,Accepted p c) :
    ∃ps,DecodedList cs ps ∧
      (∀q∈ps,SchedPubOk q.1) ∧
      (∀q∈ps,∀tau,∃r,ActualRun.run (ProcPreparedSequence.input q.1 q.2) tau=.ok r) := by
  induction cs with
  | nil => exact ⟨[],.nil,by simp,by simp⟩
  | cons c cs ih =>
    have hh := hc c (by simp)
    obtain ⟨prev,cv,st,rounds,ev,hprev,hprefix,_,_⟩ :=
      ProcActualPrefix.prepared_prefix hp c.sp hh.1 c.ctx hh.2.1 c.oldBytes c.out hh.2.2
    obtain ⟨ps,hps,hgood,hrun⟩ := ih (fun d hd=>hc d (by simp [hd]))
    have hs := prepD0_sched hp c.sp hh.1
    refine ⟨(c.sp,prev)::ps,.cons ⟨rfl,hprev⟩ hps,?_,?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hs
      · exact hgood q hq
    · intro q hq tau
      rcases List.mem_cons.mp hq with rfl|hq
      · exact ProcActualPreparedGenerator.run_success c.sp hs prev tau cv st rounds ev hprefix
      · exact hrun q hq tau

open NearSpec NearSpecV3 in
/-- Accepted ordered native scheduler calls construct a common-log22 process
trace. Other scheduler tables and global proof assembly remain separate. -/
theorem native_local {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (cs : List Call) (hc : ∀c∈cs,Accepted p c)
    (hcount : cs.length≤33) :
    ∃ps rs,DecodedList cs ps ∧
      ProcActualNativeSequence.runInputs (ProcPreparedSequence.inputs ps) 0=.ok rs ∧
      ∀t pub,TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub := by
  obtain ⟨ps,hd,hgood,hrun⟩ := native_inputs hp cs hc
  have hn : ps.length≤33 := by rw [←decoded_length hd]; exact hcount
  obtain ⟨rs,hr,hl⟩ := prepared_constructed ps hn hgood hrun
  exact ⟨ps,rs,hd,hr,hl⟩
end ZkFormal.NearV3.Candidates.ProcActualConstructedSequence
