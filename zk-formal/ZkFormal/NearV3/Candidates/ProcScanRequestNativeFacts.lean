import ZkFormal.NearV3.Candidates.ProcScanRequestLocal
import ZkFormal.NearV3.Candidates.ProcScanConvertedShape
import ZkFormal.NearV3.Candidates.ProcActualInitialPush
import ZkFormal.NearV3.Candidates.ProcActualReplayAllowance
namespace ZkFormal.NearV3.Candidates.ProcScanRequestNativeFacts
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

private theorem keys (I:Input)(cv:Array CReq)
    (h:forIn I.raw #[] (ProcActualConverted.step I)=.ok cv) :
    ∀c∈cv.toList,c.key≤I.p.maxAllowance := by
  have hf:=ProcActualInitialPush.loop_facts I cv h
  intro c hc
  obtain ⟨i,hi,he⟩:=List.getElem_of_mem hc
  have hb:i<cv.size:=by simpa using hi
  have hce:cv[i]! =c:=by simpa [getElem!_pos,hb] using he
  have hk:=(hf i hb).2.1
  rw [hce] at hk
  have ha:=ProcActualReplayAllowance.link_bound I.ids.length I.p I.allowed
    (ProcActualInput.allowances I.ids I.prev) c.link
  change (ProcActualInput.initial I).al[c.link]!≤I.p.maxAllowance at ha
  rw [hk]
  exact ha

set_option maxHeartbeats 400000 in
theorem key_bound (I:Input)(tau:Nat)(R:Run)(hr:ActualRun.run I tau=.ok R) :
    ∀c∈R.conv,c.key≤I.p.maxAllowance := by
  unfold ActualRun.run at hr
  simp only [bind,Except.bind,pure,Except.pure] at hr
  repeat first | cases hr | split at hr
  all_goals apply keys I;assumption

theorem native (I:Input)(tau:Nat)(R:Run)(hr:ActualRun.run I tau=.ok R)
    (hp:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p) :
    R.D≤4194304 ∧∀c∈R.conv,c.bits=setBits c.bm ∧c.link=c.s*R.n+c.r ∧c.key<P := by
  refine ⟨ProcScanRequestArithmetic.native_D I tau R hr hp,?_⟩
  intro c hc
  have hs:=ProcScanConvertedShape.actual I tau R hr c hc
  have hf:=ProcActualRunProjection.run_fields I tau R hr
  have hk:=key_bound I tau R hr c hc
  have hm:I.p.maxAllowance=4500000:=by rw [lp_calc hp]
  refine ⟨hs.2.1,?_,?_⟩
  · rw [hf.2.1];exact hs.2.2
  · unfold P;omega
end ZkFormal.NearV3.Candidates.ProcScanRequestNativeFacts
