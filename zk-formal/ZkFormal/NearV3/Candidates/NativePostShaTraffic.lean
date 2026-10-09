import ZkFormal.NearV3.Candidates.NativePostShaBudget
import ZkFormal.NearV3.Candidates.TrieCountTraffic
import ZkFormal.NearV3.Rcpt.Candidates.ShaAllocationTraffic

namespace ZkFormal.NearV3.Candidates.NativePostShaTraffic
open NearSpec NearSpecV3 Assembly Render.UpsGen
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- Exact physical byte sends of the count-extended node/value tables equal
the native SHA job inventory, retaining repeated occurrences and identifiers. -/
theorem bytes (ns : List NodeS3) (vs : List ValE) (hn : NodeOk ns) (hv : ValWf vs)
    (tn tv : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_BYTES true msg+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vs pub) tv pub B_BYTES true msg=
    ((Sha.Gen.expectedBytes (jobsToSha (nativeShaJobs ns vs))).map Msg.toFp).count msg := by
  rw [TrieCountTraffic.node_non_size _ _ _ _ _ _ (by decide),
    TrieCountTraffic.value_non_size _ _ _ _ _ _ (by decide)]
  rw [((TrieHeight.node_complete ns hn tn pub).2.1 B_BYTES msg).1,
    ((TrieHeight.value_complete vs ⟨hv⟩ tv pub).2.1 B_BYTES msg).1]
  rw [jobsToSha_bytes,nativeJobs_bytes ns vs hv,List.map_append,List.count_append]
  rfl

theorem accepted_bytes {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (u : Inputs) (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) (tn tv : Nat) (pub : List Fp) (msg : List Fp) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let vs:=initializeList 0 (forestNodes 0 0 0 ts)
    let es:=seedValuesFrom 0 (forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0 vs))
    let vals:=ChainMetadata.assignValues cs es
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_BYTES true msg+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vals pub) tv pub B_BYTES true msg=
      ((Sha.Gen.expectedBytes (jobsToSha (nativeShaJobs ns vals))).map Msg.toFp).count msg := by
  obtain ⟨hn,hv⟩:=NativeExecutionPost.assigned_inputs hk hw hc (by decide) hm hv u q he hb hu
  exact bytes _ _ hn hv tn tv pub msg

end ZkFormal.NearV3.Candidates.NativePostShaTraffic
