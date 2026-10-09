import ZkFormal.NearV3.Assembly.SchedulerPriorOverlay
import ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem overlay_constraints : ProcPriorCodecActualFamily.overlay.constraints=
    ProcPriorVertical4Linear.table.constraints := rfl

theorem overlay_mults : ProcPriorCodecActualFamily.overlay.interactions.flatMap Interaction.mult=
    ProcPriorVertical4Linear.table.interactions.flatMap Interaction.mult := rfl

/-- The installed presence-bus repair changes traffic routing, never local
polynomials or interaction multiplicity bits. -/
theorem overlay_local (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal ProcPriorVertical4Linear.table tr t pub) :
    TableLocal ProcPriorCodecActualFamily.overlay tr t pub := by
  refine ⟨h.1,h.2,?_,?_⟩
  · intro r hr e he
    exact h.3 r hr e (overlay_constraints ▸ he)
  · intro r hr a ha e he
    have hm:e∈ProcPriorCodecActualFamily.overlay.interactions.flatMap Interaction.mult:=
      List.mem_flatMap.mpr ⟨a,ha,he⟩
    rw [overlay_mults] at hm
    obtain ⟨a0,ha0,he0⟩:=List.mem_flatMap.mp hm
    exact h.4 r hr a0 ha0 e he0

theorem accepted_actual_prior_overlay {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧ ∀t pub,
      TableLocal ProcPriorCodecActualFamily.overlay (priorOverlay bs) t pub := by
  obtain ⟨bs,hc,hl⟩:=accepted_prior_overlay hp hk hw h hB
  exact ⟨bs,hc,fun t pub=>overlay_local _ t pub (hl t pub)⟩
end ZkFormal.NearV3.Assembly.CodecDigest
