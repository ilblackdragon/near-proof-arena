import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderRankOrigin
import ZkFormal.NearV3.Render.Ups.AcceptedTrafficList

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Shared EDGE/BMAP prefixes preserve the complete allocated native instance
contract, including actual original forest providers and byte-part inputs. -/
theorem ranked_native_allocation {us : List SchedulerUpsertWitness} {tau : Nat}
    {u : SchedulerUpsertWitness} {I : UpsInst} (h : AllocatedNativeInstance us tau u I)
    (p : List WStep3) : AllocatedNativeInstance us tau u (syncUps (rankUps p I)) := by
  obtain ⟨ht,hm,hpost,hv,hi,hproviders,hrows,hparts⟩:=h
  refine ⟨ht,hm,hpost,hv,syncUps_instOk _ (rankUps_instOk p I hi),?_,hrows,
    syncUps_parts _ (rankUps_parts p I hparts)⟩
  simpa only [NativeWalkProviders,syncUps_tau,rankUps_tau,syncUps_ts,rankUps_ts,
    syncUps_edge,rankUps_edge,syncUps_bitmap,rankUps_bitmap,syncUps_hv,rankUps_hv] using hproviders

theorem ranked_native_sha {u : SchedulerUpsertWitness} {I : UpsInst}
    (h : NativeShaFamily u I) (p : List WStep3) : NativeShaFamily u (syncUps (rankUps p I)) := by
  exact h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
