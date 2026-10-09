import ZkFormal.NearV3.Candidates.OriginalSourceNativeBudget
import ZkFormal.NearV3.Candidates.UniqueSourceNativeTotal
import ZkFormal.NearV3.Candidates.NativeEncodedBudget
namespace ZkFormal.NearV3.Candidates.OriginalSourceNativeTotal
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates

/-- Accepted native witnesses pay the original whole SIZE budget. Source
selection and byte widths are derived, not caller-supplied accounting premises. -/
theorem accepted_total {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w) (hwalk : walkD0 cb=.ok k)
    (ts : List PTrie) (store : Nat→List Bytes)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values)
    (inner bytes : Bytes) (hpub : SizeCount.countedPreparedBytes p inner=some bytes)
    (hr : Public.RootsSized p) (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K) :
    ovhNat (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)+
      DedupRender.size (DedupCompile.blocks p.lists w.entries)+
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store)≤8388608 := by
  obtain ⟨hb,_,_⟩:=DedupCompile.relD0a_inputs h hp hf hw
  have hb' : raw.length≤8388608 := by simpa only [ReexecV3D0.lenT_eq,witnessBytes] using hb
  obtain ⟨he,ha,ht,henc⟩:=UniqueSourceNativeTotal.decoded_shapes hw hb'
  exact NativeEncodedBudget.prepared_budget ts store w hs he ha ht p inner bytes hpub hr hi hk _
    (OriginalSourceNativeBudget.accepted_dictionary h hp hf hw hwalk) henc
/-- The same accepted native witness supplies receiver legality for the actual
chain-patched node/value inventory and original source compiler. -/
theorem accepted_receiver {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w) (hwalk : walkD0 cb=.ok k)
    (ts : List PTrie) (store : Nat→List Bytes)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values)
    (ht : ∀t∈ts,t.wf=true) (hb : preBytes ts≤2000000)
    (hn : NodeWf3 (forestNodes 0 0 0 ts))
    (hst : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1)
    (inner bytes : Bytes) (hpub : SizeCount.countedPreparedBytes p inner=some bytes)
    (hr : Public.RootsSized p) (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K) :
    let vs:=Assembly.forestNodes 0 0 0 ts
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    SizeCountReceiver.Valid (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes) (SizeComponents.view ns vals (DedupCompile.blocks p.lists w.entries)) (SizeComponents.counts ns vals) := by
  exact SizeChargeFields.native_valid ts store ht hb hn hst _ _
    (accepted_total h hp hf hw hwalk ts store hs inner bytes hpub hr hi hk)
end ZkFormal.NearV3.Candidates.OriginalSourceNativeTotal
