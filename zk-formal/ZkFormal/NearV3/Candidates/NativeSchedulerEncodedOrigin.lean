import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderRankList
import ZkFormal.NearV3.Render.Ups.SchedulerEncodedInstances
import ZkFormal.NearV3.Assembly.SchedulerDigestConservation
import ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic

namespace ZkFormal.NearV3.Candidates.NativeSchedulerEncodedOrigin
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates.NodePostUpdate

/-- Existing retained reader origin already contains the exact constructor
required by the scheduler digest theorem. No new execution is selected. -/
theorem encoded {us : List SchedulerUpsertWitness} {tau : Nat} {u : SchedulerUpsertWitness}
    {root : OccurrenceAddress} {I : UpsInst}
    (hu : us[tau]?=some u)
    (hr : forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root)
    (ho : NativeReaderOrigin root u.run u.value I) : NativeEncodedInstance u I := by
  have ht:=forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) tau
  rw [hr,List.getElem?_map,hu] at ht
  have he : root.tree=u.pre:=Option.some.inj ht
  obtain ⟨B,base,Qs,henc,hi⟩:=ho
  refine ⟨pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]),B,base,Qs,?_,?_⟩
  · simpa only [he] using henc
  · simpa only [he] using hi

/-- Prefix ranking preserves the existing origin; expose the encoded-instance
fact alongside allocation and SHA facts for the very same ranked list. -/
theorem ranked {us : List SchedulerUpsertWitness} {Is : List UpsInst}
    (h : ∀tau u I,us[tau]?=some u→Is[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value I)
    (p : List WStep3) :
    ∀tau u J,us[tau]?=some u→(physicalPrefixUps p Is)[tau]?=some J→
      AllocatedNativeInstance us tau u J ∧ NativeShaFamily u J ∧ NativeEncodedInstance u J := by
  intro tau u J hu hJ
  obtain ⟨ha,hs,root,hr,ho⟩ := (physicalPrefixUps_origins h p).2 tau u J hu hJ
  exact ⟨ha,hs,encoded hu hr ho⟩

/-- Apply scheduler conservation to the exact prefix-ranked and window-ranked
physical trace already used by shared allocation, using retained origin facts. -/
theorem physical_digest {us : List SchedulerUpsertWitness} {Is : List UpsInst}
    (hlen : Is.length=us.length)
    (hvalid : ∀u∈us,u.Valid ∧ u.pre.wf=true)
    (h : ∀tau u I,us[tau]?=some u→Is[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value I)
    (p : List WStep3) (hR : UpsRelay.compactR (physicalPrefixUps p Is)≤2^22)
    (t : Nat) (pub msg : List ZkFormal.Algebra.Fp)
    (hl : TableLocal UpsRelay.compactTable (CompactHeight.trace (physicalPrefixUps p Is)) t pub)
    (rank : Nat→Nat) :
    ZkFormal.Air.tableBusCount UpsRelay.compactTable.interactions
      (patchWindowCounters (CompactHeight.trace (physicalPrefixUps p Is)) t rank) t pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests (schedulerShaJobs 0 us)).map Msg.toFp).count msg := by
  rw [WindowPatchOtherTraffic.count hl rank B_DIGEST (by decide) false msg]
  exact scheduler_compact_digest_count us (physicalPrefixUps p Is)
    ((physicalPrefixUps_origins h p).1.trans hlen) hvalid (ranked h p) hR t pub msg

end ZkFormal.NearV3.Candidates.NativeSchedulerEncodedOrigin
