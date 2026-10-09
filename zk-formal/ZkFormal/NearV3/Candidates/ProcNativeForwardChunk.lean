import ZkFormal.NearV3.Candidates.ProcNativeForwardRuntime
import ZkFormal.NearV3.Candidates.ProcNativeForwardInitial
namespace ZkFormal.NearV3.Candidates.ProcNativeForwardChunk
open NearSpec NearSpecV3 NearSpec.TransferV1 ProcNativeForwardSize

private theorem bind_ok {α β : Type} {a : Except String α}
    {f : α→Except String β} {b : β} (h:a.bind f=.ok b) :
    ∃x,a=.ok x ∧ f x=.ok b := by cases a <;> simp_all [Except.bind]

/-- The scheduler output and forwarding limits come from the same successful
native new-chunk execution, with the exact outgoing receipt sequence. -/
theorem chunk_forward (ps : Prims) (ctx : ApplyCtx) (t : PTrie) (rs : List Receipt)
    (out : MainOut) (h:applyNewChunk ps ctx t rs=.ok out) :
    ∃mid so finalLimits,schedStep ps ctx t=.ok (mid,so) ∧
      forwardAll ctx (ProcNativeForwardInitial.limits ps ctx so) out.outgoing=some finalLimits := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨⟨mid,so⟩,hs,h⟩:=bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨⟨acc,ls⟩,ha,h⟩:=bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  refine ⟨mid,so,ls,hs,?_⟩
  have hf:=ProcNativeForwardRuntime.appended_refunds ctx rs 0 _ (acc,ls) ha
  simpa [ProcNativeForwardInitial.limits] using hf

/-- Every native forwarding demand is bounded by that execution's scheduler
grant; no independent limit/receipt correspondence assumption is needed. -/
theorem chunk_demand_grant (ps : Prims) (ctx : ApplyCtx) (t : PTrie) (rs : List Receipt)
    (out : MainOut) (h:applyNewChunk ps ctx t rs=.ok out) :
    ∃mid so,schedStep ps ctx t=.ok (mid,so) ∧
      ∀d∈fwdSizes ctx out.outgoing,d.2≤so.grant ctx.own d.1 := by
  obtain ⟨mid,so,ls,hs,hf⟩:=chunk_forward ps ctx t rs out h
  exact ⟨mid,so,hs,fun d hd=>ProcNativeForwardInitial.demand_grant ps ctx so out.outgoing ls hf d hd⟩

/-- A separately exposed scheduler result is uniquely the one used for forwarding. -/
theorem same_scheduler_grant (ps : Prims) (ctx : ApplyCtx) (t mid : PTrie)
    (so : SchedOut) (rs : List Receipt) (out : MainOut)
    (h:applyNewChunk ps ctx t rs=.ok out) (hs:schedStep ps ctx t=.ok (mid,so))
    (d : Nat×Nat) (hd:d∈fwdSizes ctx out.outgoing) : d.2≤so.grant ctx.own d.1 := by
  obtain ⟨mid',so',hs',hb⟩:=chunk_demand_grant ps ctx t rs out h
  have he:=Except.ok.inj (hs'.symm.trans hs)
  have he':so'=so:=congrArg Prod.snd he
  subst so'
  exact hb d hd
end ZkFormal.NearV3.Candidates.ProcNativeForwardChunk
