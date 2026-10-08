import ZkFormal.NearV3.Candidates.SchedulerShaSplit
import ZkFormal.NearV3.Assembly.SchedulerSanityJobs

namespace ZkFormal.NearV3.Candidates.SchedulerPhysicalShaSplit
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Render.UpsGen Render.UpsRelay

/-- The actual compact UPS trace discharges the output-node portion of the
whole scheduler SHA inventory. Fresh value and sanity producers remain explicit. -/
theorem bytes {us : List SchedulerUpsertWitness} {insts : List Render.UpsInst}
    (hl : insts.length=us.length)
    (ha : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I)
    (hR : compactR insts≤2^22) (t : Nat) (pub : List Fp) (msg : List Fp) :
    ((Sha.Gen.expectedBytes (schedulerShaJobs 0 us++schedulerSanityJobs 0 us)).map Msg.toFp).count msg=
      tableBusCount compactTable.interactions (CompactHeight.trace insts) t pub B_BYTES true msg+
      ((Sha.Gen.expectedBytes (SchedulerShaSplit.freshJobs 0 us++schedulerSanityJobs 0 us)).map Msg.toFp).count msg := by
  have hp:=SchedulerShaSplit.partition 0 us
  rw [SchedulerShaSplit.nodes] at hp
  have hb:=hp.flatMap_right (fun M=>(List.range M.bytes.length).map fun p=>[M.id,p,M.bytes.getD p 0])
  change (Sha.Gen.expectedBytes (schedulerShaJobs 0 us)).Perm
    (Sha.Gen.expectedBytes (SchedulerShaSplit.freshJobs 0 us++compactNodeJobs us)) at hb
  have hc:=(hb.map Msg.toFp).count_eq msg
  rw [CompactPhysicalShaBytes.native_bytes hl ha hR t pub msg]
  simp only [Sha.Gen.expectedBytes,List.flatMap_append,List.map_append,List.count_append] at hc ⊢
  omega

theorem allocated {us : List SchedulerUpsertWitness} {insts : List Render.UpsInst}
    (hl : insts.length=us.length) (hpos : 1≤us.length) (hlen : us.length≤32)
    (ha : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I)
    (hout : (us.map (fun u=>outputByteCharge u.run)).sum≤2131072)
    (t : Nat) (pub : List Fp) :
    TableLocal compactTable (CompactHeight.trace insts) t pub ∧
    ∀msg,((Sha.Gen.expectedBytes (schedulerShaJobs 0 us++schedulerSanityJobs 0 us)).map Msg.toFp).count msg=
      tableBusCount compactTable.interactions (CompactHeight.trace insts) t pub B_BYTES true msg+
      ((Sha.Gen.expectedBytes (SchedulerShaSplit.freshJobs 0 us++schedulerSanityJobs 0 us)).map Msg.toFp).count msg := by
  have hcap : compactR insts+1≤2^22 := by
    rw [compact_rows_exact hl (fun tau u I hu hI=>(ha tau u I hu hI).1)]
    exact compact_rows_fit hlen hout
  exact ⟨(CompactPhysicalShaBytes.allocated hl hpos hlen ha hout t pub).1,
    fun msg=>bytes hl ha (by omega) t pub msg⟩

end ZkFormal.NearV3.Candidates.SchedulerPhysicalShaSplit
