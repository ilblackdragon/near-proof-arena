import ZkFormal.NearV3.Assembly.PrepBodyComplete
import ZkFormal.NearV3.Candidates.QueueKeyRepairTransport
import ZkFormal.NearV3.Candidates.NativeQueueCounters
import ZkFormal.NearV3.Candidates.NativeSizeConstruction
namespace ZkFormal.NearV3.Candidates.NativeRepairedQueueLocal
open Rcpt.Candidates.NodePostUpdate Render.UpsGen NearSpec NearSpecV3 ZkFormal.Near Assembly ZkFormal.Air ZkFormal.Algebra Qv Qv.Candidates Qv.Candidates.CombinedWalkGen

theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness} {p : Prep}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w) (hc:checkD0a B0 cb wb=.ok ())
    (hm:m.NativeValid k w)
    (hv:ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hp:prepD0 cb (nativeHint k w m)=.ok p)
    (v : MainValues) (hvalid:v.Valid) (hreads:v.Reads m.pre m.pre m.pre) (overhead : Nat) :
    let pres:=steps.map ImplicitStepV3.pre
    let ws:=plan m.pre v pres (NativeQueueIds.resolve m.pre v pres)
    let vs:=queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))
    let tr:=mixedTrace ws vs 22
    let pub:=ZkFormal.Udr.pubOf Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)
    TableLocal QueueKeyRepair.table tr 0 pub ∧
      ∀msg,tableBusCount QueueKeyRepair.interactions tr 0 pub ValueTable.B_QVC true msg=
        tableBusCount QueueKeyRepair.interactions tr 0 pub ValueTable.B_QVC false msg := by
  have hrel:RelD0a B0 cb wb:=(relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,hr,_,hpk⟩:=NativeSizeConstruction.public_fields hrel hp hw hk
  have hcheck:=hc
  unfold checkD0a at hcheck
  obtain ⟨u,hcheck,_⟩:=ReexecV3D0.bind_ok' hcheck
  cases u
  obtain ⟨_,_,_,_,hcnt,hK⟩:=checkD0_native_steps hk hw hcheck
  have hl:=hv.length
  simp only [List.length_zip] at hl
  have hcK:steps.length=p.hdr.K:=by omega
  have hK32:p.hdr.K<256^4:=by omega
  have ht:=NativeQueueCounters.accepted hk hw hc hm hv v hvalid hreads
    ⟨.delayed,0,0,0,none,0,0,false,false⟩
    (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead hr hK32 hcK
  refine ⟨QueueKeyRepair.local_transport _ _ _ ht.1,?_⟩
  intro msg
  rw [QueueKeyRepair.nonkey_count _ _ _ _ (by decide),QueueKeyRepair.nonkey_count _ _ _ _ (by decide)]
  rw [tableBusCount_eq,tableBusCount_eq]
  exact ht.2.2.count_eq msg
end ZkFormal.NearV3.Candidates.NativeRepairedQueueLocal
