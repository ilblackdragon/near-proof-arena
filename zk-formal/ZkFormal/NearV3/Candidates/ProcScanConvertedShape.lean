import ZkFormal.NearV3.Candidates.ProcActualConvertedFacts
namespace ZkFormal.NearV3.Candidates.ProcScanConvertedShape
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Shape (I:Input)(c:CReq) :=
  c.bm.length=5 ∧c.bits=setBits c.bm ∧c.link=c.s*I.ids.length+c.r

def All (I:Input)(cs:Array CReq) := ∀c∈cs.toList,Shape I c

theorem step (I:Input)(q:RawReq)(cs:Array CReq)(hs:All I cs)(out:ForInStep (Array CReq))
    (h:ProcActualConverted.step I q cs=.ok out) : ExceptLoop.StepInv (All I) out := by
  unfold ProcActualConverted.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | change All I (cs.push _)
      intro c hc
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hc
      rcases hc with hc|rfl
      · exact hs c hc
      · have hcheck:check (q.bm.length==5) "bitmap length ≠ 5"=.ok ():=by assumption
        have hb:=ProcActualReplayShape.check_true _ _ hcheck
        simp only [beq_iff_eq] at hb
        exact ⟨hb,rfl,rfl⟩

theorem loop (I:Input)(cs:Array CReq)
    (h:forIn I.raw #[] (ProcActualConverted.step I)=.ok cs) : All I cs :=
  ExceptLoop.invariant I.raw (ProcActualConverted.step I) (All I)
    (fun q _ a ha out ho=>step I q a ha out ho) #[] cs (by intro c h;cases h) h

set_option maxHeartbeats 400000 in
theorem actual (I:Input)(tau:Nat)(R:Run)(h:ActualRun.run I tau=.ok R) :
    ∀c∈R.conv,Shape I c := by
  unfold ActualRun.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals apply loop I; assumption
end ZkFormal.NearV3.Candidates.ProcScanConvertedShape
