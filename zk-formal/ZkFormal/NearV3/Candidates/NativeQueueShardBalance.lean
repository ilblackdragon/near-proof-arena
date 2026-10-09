import ZkFormal.NearV3.Candidates.NativeQueueCounters
import ZkFormal.NearV3.Candidates.QueueKeyRepairTransport
import ZkFormal.NearV3.Assembly.QueueShardBalance
namespace ZkFormal.NearV3.Candidates.NativeQueueShardBalance
open NearSpec NearSpecV3 ZkFormal.Near Assembly ZkFormal.Air ZkFormal.Algebra Qv Qv.Candidates Qv.Candidates.CombinedWalkGen

theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (hc:checkD0a B0 cb wb=.ok ())
    (hm:m.NativeValid k w)
    (hv:ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid:v.Valid) (hreads:v.Reads m.pre m.pre m.pre) (pub : List Fp) :
    let pres:=steps.map ImplicitStepV3.pre
    let ws:=plan m.pre v pres (NativeQueueIds.resolve m.pre v pres)
    let vs:=queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))
    let tr:=mixedTrace ws vs 22
    ∀msg,tableBusCount QueueKeyRepair.interactions tr 0 pub B_QSH true msg=
      tableBusCount QueueKeyRepair.interactions tr 0 pub B_QSH false msg := by
  obtain ⟨hr,hfit⟩:=NativeQueueCounters.accepted_records hk hw hc hm hv v hvalid hreads
  have hh:=NativeQueueLookupBinding.native_holds hv v hvalid hreads
  have hb:=plan_physical_qsh_balance _ (NativeQueueIds.resolve _ _ _) hh 22 pub hr hfit
  dsimp only
  intro msg
  rw [QueueKeyRepair.nonkey_count _ _ _ _ (by decide),QueueKeyRepair.nonkey_count _ _ _ _ (by decide)]
  rw [tableBusCount_eq,tableBusCount_eq]
  exact hb.count_eq msg
end ZkFormal.NearV3.Candidates.NativeQueueShardBalance
