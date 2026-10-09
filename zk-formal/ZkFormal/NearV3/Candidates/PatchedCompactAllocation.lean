import ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic
import ZkFormal.NearV3.Candidates.SchedulerPhysicalShaSplit
import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowBalance

namespace ZkFormal.NearV3.Candidates.PatchedCompactAllocation
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Render.UpsGen Render.UpsRelay
open Rcpt.Candidates.NodePostUpdate

/-- One physical compact trace supplies local legality, exact scheduler node SHA
bytes and ranked UPB balance simultaneously. Provider ownership and uniqueness
are explicit remaining obligations; the counter patch preserves all other buses. -/
theorem allocated {us : List SchedulerUpsertWitness} {insts : List Render.UpsInst}
    (hl : insts.length=us.length) (hpos : 1≤us.length) (hlen : us.length≤32)
    (ha : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I)
    (hout : (us.map (fun u=>outputByteCharge u.run)).sum≤2131072)
    (t : Nat) (pub : List Fp) (es : List Msg) (hn : es.Nodup)
    (hc : ∀r∈physicalWindowRows (CompactHeight.trace insts) t,
      physicalWindowKey (CompactHeight.trace insts) t r∈es) :
    let original:=CompactHeight.trace insts
    let patched:=patchWindowCounters original t (physicalWindowRank original t)
    patched.log t=22 ∧ TableLocal compactTable patched t pub ∧
    (∀b,b≠B_UPB→∀sd msg,tableBusCount compactTable.interactions patched t pub b sd msg=
      tableBusCount compactTable.interactions original t pub b sd msg) ∧
    (∀msg,((Sha.Gen.expectedBytes (schedulerShaJobs 0 us++schedulerSanityJobs 0 us)).map Msg.toFp).count msg=
      tableBusCount compactTable.interactions patched t pub B_BYTES true msg+
      ((Sha.Gen.expectedBytes (SchedulerShaSplit.freshJobs 0 us++schedulerSanityJobs 0 us)).map Msg.toFp).count msg) ∧
    (∀msg,((es.map (fun e=>e++[0])).map Msg.toFp).count msg+
      tableBusCount compactTable.interactions patched t pub B_UPB true msg=
      tableBusCount compactTable.interactions patched t pub B_UPB false msg+
      ((es.map (fun e=>e++[physicalWindowUsers original t e])).map Msg.toFp).count msg) := by
  obtain ⟨hlocal,hbytes⟩:=SchedulerPhysicalShaSplit.allocated hl hpos hlen ha hout t pub
  refine ⟨rfl,patchWindowCounters_local hlocal _,?_,?_,?_⟩
  · intro b hb sd msg
    exact WindowPatchOtherTraffic.count hlocal _ b hb sd msg
  · intro msg
    rw [WindowPatchOtherTraffic.count hlocal _ B_BYTES (by decide)]
    exact hbytes msg
  · intro msg
    exact window_counter_field_balance _ t pub es hn hc msg

end ZkFormal.NearV3.Candidates.PatchedCompactAllocation
