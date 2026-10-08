import ZkFormal.NearV3.Candidates.ExceptLoop
import ZkFormal.NearV3.Sched.Spec.Conv
namespace ZkFormal.NearV3.Candidates.ProcConverted
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- The actual first loop body of Gen.run, kept separate for its invariant. -/
def step (I : Input) (q : RawReq) (conv : Array CReq) : Except String (ForInStep (Array CReq)) := do
  let bits := setBits q.bm
  if bits.isEmpty then return .yield conv
  check (q.bm.length == 5) "bitmap length ≠ 5"
  check (q.s < I.ids.length && q.r < I.ids.length) "shard index"
  let link := q.s * I.ids.length + q.r
  return .yield (conv.push ⟨conv.size,q.s,q.r,link,q.bm,bits,incsOf I.p q.bm,
    (linkPass I.ids.length I.p I.allowed (a0Src I.ids I.prev)).a2[link]!⟩)

def Bounded (conv : Array CReq) : Prop := ∀c∈conv.toList,c.incs.length≤40

theorem step_bounded (I : Input) (q : RawReq) (conv : Array CReq) (hb : Bounded conv)
    (out : ForInStep (Array CReq)) (h : step I q conv=.ok out) : ExceptLoop.StepInv Bounded out := by
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hb
    | change Bounded (conv.push _)
      intro c hc
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hc
      rcases hc with hc|rfl
      · exact hb c hc
      · exact incsOf_length_le _ _

theorem loop_bounded (I : Input) (out : Array CReq)
    (h : forIn I.raw #[] (step I)=.ok out) : Bounded out :=
  ExceptLoop.invariant I.raw (step I) Bounded
    (fun q _ conv hb out ho=>step_bounded I q conv hb out ho) #[] out (by simp [Bounded]) h

set_option maxHeartbeats 400000 in
/-- The request bound is derived from the exact executed conversion loop, with no
assumption about its resulting CReq records. -/
theorem run_converted (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∀c∈R.conv,c.incs.length≤40 := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    apply loop_bounded I
    assumption
end ZkFormal.NearV3.Candidates.ProcConverted
