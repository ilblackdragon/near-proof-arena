import ZkFormal.NearV3.Candidates.NativeShaLengths
import ZkFormal.NearV3.Candidates.NativePostBytes
import ZkFormal.NearV3.Rcpt.Candidates.ShaJobBridge
import ZkFormal.NearV3.Assembly.ShaBinRender

namespace ZkFormal.NearV3.Candidates.NativePostShaOk
open ZkFormal.Air ZkFormal.Algebra
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (u : Inputs) (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let vs:=initializeList 0 (forestNodes 0 0 0 ts)
    let es:=seedValuesFrom 0 (forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0 vs))
    let vals:=ChainMetadata.assignValues cs es
    ZkFormal.Sha.MsgsOk (jobsToSha (nativeShaJobs ns vals)) := by
  have hgood : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  obtain ⟨hn,hval⟩:=NativeExecutionPost.assigned_inputs hk hw hc (by decide) hm hv u q he hb hu
  dsimp only
  constructor
  · intro M hM
    obtain ⟨job,hjob,rfl⟩:=List.mem_map.mp hM
    exact NativePostBytes.jobs_bytes _ hgood _ u q job hjob
  · intro M hM
    obtain ⟨job,hjob,rfl⟩:=List.mem_map.mp hM
    exact NativeShaLengths.jobs_length _ _ hn.wf hval job hjob
  · rw [jobsToSha_rows]
    have hh:=NativePostShaBudget.accepted hk hw hc hm hv u q he hb hu
    change _≤2^22
    exact Nat.le_trans hh (by decide)

theorem complete {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (u : Inputs) (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) (pub : List Fp) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let vs:=initializeList 0 (forestNodes 0 0 0 ts)
    let es:=seedValuesFrom 0 (forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0 vs))
    let vals:=ChainMetadata.assignValues cs es
    let jobs:=jobsToSha (nativeShaJobs ns vals)
    TableLocal (ZkFormal.Sha.Table.table B_BYTES B_DIGEST) (shaBinTrace [jobs]) 0 pub ∧
    TableTraffic (ZkFormal.Sha.Table.interactions B_BYTES B_DIGEST) (shaBinTrace [jobs]) 0 pub (shaBinTraffic jobs) := by
  have hok:=accepted hk hw hc hm hv u q he hb hu
  exact ⟨shaBin_local [_] 0 pub hok,shaBin_traffic [_] 0 pub hok⟩

end ZkFormal.NearV3.Candidates.NativePostShaOk
