import ZkFormal.NearV3.Candidates.NativeSourceFour
import ZkFormal.NearV3.Candidates.NativeExecutionSize
import ZkFormal.NearV3.Candidates.NodeUseSize
namespace ZkFormal.NearV3.Candidates.NativeExecutionUsage
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
theorem inputs {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (hB : B≤2000000)
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let vs:=initializeList 0 (forestNodes 0 0 0 ts)
    let es:=seedValuesFrom 0 (forestBytes ts)
    NodeOk vs ∧ ValWf es := by
  have hc : checkD0 cb wb=.ok () := by
    have hh:=((relD0a_iff B cb wb).mpr h).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hc
  have hbound:=Nat.le_trans (checkD0a_preBytes hk hw h hm hv) hB
  have htrees : ∀tr∈m.pre::steps.map ImplicitStepV3.pre,tr.wf=true := by
    intro tr hr
    rcases List.mem_cons.mp hr with rfl|hr
    · rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hr
      exact (hv.input_facts s hs).2.2
  refine ⟨NativeNodeLocal.native_ok _ htrees hbound (NativeExecutionNodeLocal.depth hm hv)
    ?_ (NativeExecutionNodeLocal.nonempty hm _),NativeValueWf.forest_wf _ htrees hbound⟩
  have hs:=hv.length
  simp only [List.length_zip] at hs
  change (steps.map ImplicitStepV3.pre).length+1≤2013265921
  simp only [List.length_map]
  omega

theorem assigned_inputs {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (hB : B≤2000000)
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let vs:=initializeList 0 (forestNodes 0 0 0 ts)
    let es:=seedValuesFrom 0 (forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    NodeOk (assignList q 0 (ChainMetadata.assign cs 0 vs)) ∧ ValWf (ChainMetadata.assignValues cs es) := by
  obtain ⟨hn,hval⟩:=inputs hk hw h hB hm hv
  have hids:=(StoreClassPartition.combined_metadata _ (NativeStoreProvenance.valueTau (m.pre::steps.map ImplicitStepV3.pre)) _ hn.wf hval).2.1
  exact ⟨NodeUseLocal.node_ok q _ (ChainMetadata.node_ok _ _ hn hids) he hb hu,
    ChainMetadata.value_wf _ _ hval hids⟩

theorem complete {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (hB : budget≤2000000)
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) (t : Nat) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    let vs:=NodePostUpdate.initializeList 0 (Assembly.forestNodes 0 0 0 ts)
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=assignList q 0 (ChainMetadata.assign cs 0 vs)
    let vals:=ChainMetadata.assignValues cs es
    let pub:=ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes
    let v:=SizeComponents.view ns vals (DedupCompile.blocks p.lists w.entries)
    let counts:=SizeComponents.counts ns vals
    TableLocal SizeCount.nodeTable (TrieCountHeight.node ns pub) t pub ∧
    TableLocal SizeCount.valTable (TrieCountHeight.value vals pub) t pub ∧
    TableLocal SizeCount.sizeTable (SizeCountReceiver.trace pub v counts) t pub ∧
    TableTraffic SizeCount.sizeTable.interactions (SizeCountReceiver.trace pub v counts) t pub
      (SizeCountReceiver.traffic v counts) := by
  have hdecode : decodeW wb=.ok w := by
    unfold decodeW
    rw [hf]
    change decodeStateWitness raw=.ok w
    exact hw
  obtain ⟨hn,hval⟩:=assigned_inputs hk hdecode ((relD0a_iff budget cb wb).mp h) hB hm hv q he hb hu
  have hreceiver:=NodeUseSize.receiver q _ _ _ _ (NativeExecutionSize.receiver h hp hf hw hk hB hm hv)
  exact ⟨TrieCountHeight.node_local _ hn _ _,TrieCountHeight.value_local _ ⟨hval⟩ _ _,
    SizeComponents.receiver_complete _ _ _ _ hreceiver t⟩

theorem size_balance {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (hB : budget≤2000000)
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) (tn tv tsize : Nat) (msg : List Algebra.Fp) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    let vs:=NodePostUpdate.initializeList 0 (Assembly.forestNodes 0 0 0 ts)
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=assignList q 0 (ChainMetadata.assign cs 0 vs)
    let vals:=ChainMetadata.assignValues cs es
    let pub:=ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes
    let v:=SizeComponents.view ns vals (DedupCompile.blocks p.lists w.entries)
    let counts:=SizeComponents.counts ns vals
    let src:=NativeSourceFour.trace (DedupCompile.blocks p.lists w.entries) (sourceRepeated p.lists)
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_SIZE true msg+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vals pub) tv pub B_SIZE true msg+
      SourceSizeTraffic.fourCount src 0 1 2 3 pub true msg+
      tableBusCount SizeCount.sizeTable.interactions (SizeCountReceiver.trace pub v counts) tsize pub B_SIZE true msg=
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_SIZE false msg+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vals pub) tv pub B_SIZE false msg+
      SourceSizeTraffic.fourCount src 0 1 2 3 pub false msg+
      tableBusCount SizeCount.sizeTable.interactions (SizeCountReceiver.trace pub v counts) tsize pub B_SIZE false msg := by
  have hdecode : decodeW wb=.ok w := by
    unfold decodeW
    rw [hf]
    change decodeStateWitness raw=.ok w
    exact hw
  obtain ⟨hn,hval⟩:=assigned_inputs hk hdecode ((relD0a_iff budget cb wb).mp h) hB hm hv q he hb hu
  exact NativeSourceFour.balance h hp hf hw _ _ hn ⟨hval⟩ _ tn tv tsize msg

end ZkFormal.NearV3.Candidates.NativeExecutionUsage
