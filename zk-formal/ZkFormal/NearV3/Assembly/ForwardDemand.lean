import ZkFormal.NearV3.Assembly.ForwardBytes
import ZkFormal.NearV3.Assembly.NativeSchedulerBounds

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

/-- The native preparation demand guard follows from actual successful runtime
forwarding and the scheduler's computed grant bound, with no extra cap premise. -/
theorem applyNewChunk_fwdDemand_guard {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs = .ok out) :
    ((fwdLinks ctx out.outgoing).all fun (_,d) => decide (d < fwdDemandMax)) = true := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨mid,so⟩,hs,h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨acc,ls⟩,ha,h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h
  obtain ⟨added,he,hf⟩ := applyReceipts_forwardRun ctx rs 0 _ _ _ ha
  simp only [List.nil_append] at he
  rw [he]
  apply forwardRun_demand_guard hf
  intro l hl
  obtain ⟨⟨s,ci,missed⟩,_,rfl⟩ := List.mem_map.mp hl
  exact schedStep_grant_bound hs ctx.own s

end ZkFormal.NearV3.Assembly
