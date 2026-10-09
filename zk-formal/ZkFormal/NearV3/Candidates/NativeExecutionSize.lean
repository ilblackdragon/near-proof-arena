import ZkFormal.NearV3.Candidates.NativeExecutionStores
namespace ZkFormal.NearV3.Candidates.NativeExecutionSize
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates
/-- The actual accepted execution forest pays and constructs the SIZE receiver;
no caller-supplied forest accounting, shape or store alignment remains. -/
theorem receiver {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (hB : budget≤2000000)
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    let vs:=NodePostUpdate.initializeList 0 (Assembly.forestNodes 0 0 0 ts)
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    SizeCountReceiver.Valid (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)
      (SizeComponents.view ns vals (DedupCompile.blocks p.lists w.entries)) (SizeComponents.counts ns vals) := by
  have hdecode : decodeW wb=.ok w := by
    unfold decodeW
    rw [hf]
    change decodeStateWitness raw=.ok w
    exact hw
  have hc : checkD0 cb wb=.ok () := by
    have hh:=h.1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,hK,_⟩:=checkD0_native_steps hk hdecode hc
  have hl : (m.pre::steps.map ImplicitStepV3.pre).length=(transitions w).length := by
    have hs:=hv.length
    simp only [List.length_zip,hK,Nat.min_self] at hs
    simp only [List.length_cons,List.length_map,transitions]
    omega
  apply InitializedNativeSize.receiver h hp hf hw hk _ hl _
    (Nat.le_trans (checkD0a_preBytes hk hdecode ((relD0a_iff budget cb wb).mp h) hm hv) hB)
    (NativeExecutionNodeLocal.depth hm hv) (NativeExecutionStores.stores hm hv hK)
  intro tr hr
  rcases List.mem_cons.mp hr with rfl|hr
  · rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
  · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hr
    exact (hv.input_facts s hs).2.2

/-- Node, value and SIZE certificates use the same native forest and public input. -/
theorem complete {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (hB : budget≤2000000)
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) (t : Nat) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    let vs:=NodePostUpdate.initializeList 0 (Assembly.forestNodes 0 0 0 ts)
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
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
  obtain ⟨hn,hvlocal⟩:=NativeExecutionNodeLocal.complete hk hdecode
    ((relD0a_iff budget cb wb).mp h) hB hm hv t
    (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp (Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)))
  exact ⟨hn,hvlocal,SizeComponents.receiver_complete _ _ _ _
    (receiver h hp hf hw hk hB hm hv) t⟩

end ZkFormal.NearV3.Candidates.NativeExecutionSize
