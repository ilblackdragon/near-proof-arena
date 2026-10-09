import ZkFormal.NearV3.Candidates.InitializedSizeValid
import ZkFormal.NearV3.Candidates.NativeSizeConstruction
namespace ZkFormal.NearV3.Candidates.InitializedNativeSize
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates
/-- Accepted native SIZE construction uses initialized metadata; no raw forest
NodeWf premise is required. Native cardinality supplies the forest-count bound. -/
theorem receiver {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (ts : List PTrie) (hl : ts.length=(transitions w).length)
    (ht : ∀t∈ts,t.wf=true) (hb : preBytes ts≤2000000)
    (hd : ∀t∈ts,∀key,fdepth t key≤trieFuel)
    (hst : ∀p∈ts.zipIdx,Stored
      (mkStore ((((transitions w)[p.2]?).map Transition.values).getD [])) p.1) :
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
  obtain ⟨_,_,_,_,hK,hbound⟩:=checkD0_native_steps hk hdecode hc
  have htlen : ts.length≤ZkFormal.Algebra.P := by
    simp only [transitions,List.length_cons] at hl
    change ts.length≤2013265921
    omega
  exact InitializedSizeValid.native_valid ts _ ht hb hd htlen hst _ _
    (NativeSizeConstruction.total h hp hf hw hk ts hl)

theorem local_complete {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (ts : List PTrie) (hl : ts.length=(transitions w).length)
    (ht : ∀t∈ts,t.wf=true) (hb : preBytes ts≤2000000)
    (hd : ∀t∈ts,∀key,fdepth t key≤trieFuel)
    (hst : ∀p∈ts.zipIdx,Stored
      (mkStore ((((transitions w)[p.2]?).map Transition.values).getD [])) p.1) (t : Nat) :
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    let vs:=NodePostUpdate.initializeList 0 (Assembly.forestNodes 0 0 0 ts)
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    let pub:=ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes
    let v:=SizeComponents.view ns vals (DedupCompile.blocks p.lists w.entries)
    let counts:=SizeComponents.counts ns vals
    ZkFormal.Near.TableLocal SizeCount.sizeTable (SizeCountReceiver.trace pub v counts) t pub ∧
      ZkFormal.Near.TableTraffic SizeCount.sizeTable.interactions
        (SizeCountReceiver.trace pub v counts) t pub (SizeCountReceiver.traffic v counts) := by
  exact SizeComponents.receiver_complete _ _ _ _ (receiver h hp hf hw hk ts hl ht hb hd hst) t

end ZkFormal.NearV3.Candidates.InitializedNativeSize
