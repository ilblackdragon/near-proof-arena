import ZkFormal.NearV3.Candidates.NativeQueueCounters
import ZkFormal.NearV3.Candidates.NativeValueByteInventory
import ZkFormal.NearV3.Assembly.QueueValueBytes

namespace ZkFormal.NearV3.Candidates.NativeQueueBytes
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates
open Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Algebra ValueGen

/-- Queue byte traffic is tied to the same native value occurrences as the
lookup and counter trace; repeated reads do not duplicate the byte provider. -/
theorem accepted_inventory {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre)
    (pub : List Fp) :
    let pres := steps.map ImplicitStepV3.pre
    let ws := plan m.pre v pres (NativeQueueIds.resolve m.pre v pres)
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))
    ∃ msgs, msgs.Sublist ((valRecvs (forestStoreViews (m.pre::pres)).values B_VBYTES).map Msg.toFp) ∧
      ((List.range (2^22)).flatMap (fun r =>
        rowTraffic CombinedTable.interactions (mixedTrace ws vs 22) 0 r pub B_VBYTES true)).Perm msgs := by
  obtain ⟨hr,hfit⟩ := NativeQueueCounters.accepted_records hk hw hc hm hv v hvalid hreads
  exact plan_physical_vbytes_inclusion _ _
    (queueForestProviders_accepts _ 0 0 (NativeQueueLookupBinding.native_holds hv v hvalid hreads))
    (checkD0a_queue_provider_bytes hk hw hc hm hv v) 22 pub hr hfit

/-- Every field packet emitted by the physical queue parser is accounted for
in the actual physical EmptyValue demand. This is inclusion, not a global
partition: disjointness from account/key providers remains to be established. -/
theorem physical_bound {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre)
    (cs : List StoreDuplicateChain.Entry)
    (hval : Render.ValOk (ChainMetadata.assignValues cs
      (seedValuesFrom 0 (forestBytes (m.pre::steps.map ImplicitStepV3.pre)))))
    (tv : Nat) (pub msg : List Fp) :
    let pres := steps.map ImplicitStepV3.pre
    let ws := plan m.pre v pres (NativeQueueIds.resolve m.pre v pres)
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))
    tableBusCount CombinedTable.interactions (mixedTrace ws vs 22) 0 pub B_VBYTES true msg ≤
      tableBusCount EmptyValue.table.interactions
        (TrieCountHeight.value (ChainMetadata.assignValues cs
          (seedValuesFrom 0 (forestBytes (m.pre::pres)))) pub) tv pub B_VBYTES false msg := by
  obtain ⟨msgs,hsub,hperm⟩ := accepted_inventory hk hw hc hm hv v hvalid hreads pub
  have hn := hsub.count_le msg
  have he := hperm.count_eq msg
  dsimp only
  rw [NativeValueByteInventory.physical _ cs hval tv pub msg]
  rw [ZkFormal.Near.tableBusCount_eq]
  simp only [Trace.height,mixedTrace] at he ⊢
  rw [he]
  simpa only [forestStoreViews,NativeValueByteInventory.seed,cnt] using hn

end ZkFormal.NearV3.Candidates.NativeQueueBytes
