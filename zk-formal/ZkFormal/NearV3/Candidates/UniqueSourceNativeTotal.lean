import ZkFormal.NearV3.Candidates.UniqueSourceNativeBudget
import ZkFormal.NearV3.Candidates.UniqueSizeValid
namespace ZkFormal.NearV3.Candidates.UniqueSourceNativeTotal
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates

theorem decoded_shapes {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw=.ok w) (hb : raw.length≤8388608) :
    w.epochId.length=32 ∧ w.appliedReceiptsHash.length=32 ∧
      (∀t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32) ∧
      (ZkFormal.V3.encodeSW w).length≤8388608 := by
  have hs:=decodeStateWitness_shape hw hb
  simp only [ZkFormal.V3.D0Shape,ZkFormal.V3.D0Shape.wf,Bool.and_eq_true] at hs
  have he : ZkFormal.V3.h32 w.epochId=true := by grind only
  have ha : ZkFormal.V3.h32 w.appliedReceiptsHash=true := by grind only
  have hm : ZkFormal.V3.transitionWf w.main=true := by grind only
  have hi : w.implicit.all ZkFormal.V3.transitionWf=true := by grind only
  refine ⟨ZkFormal.V3.h32_len he,ZkFormal.V3.h32_len ha,?_,?_⟩
  · intro t ht
    have htw : ZkFormal.V3.transitionWf t=true := by
      rcases List.mem_cons.mp ht with rfl|ht
      · exact hm
      · exact List.all_eq_true.mp hi t ht
    simp only [ZkFormal.V3.transitionWf,Bool.and_eq_true] at htw
    exact ⟨ZkFormal.V3.h32_len htw.1.1.1,ZkFormal.V3.h32_len htw.2⟩
  · have hh:=decodeStateWitness_encodeSW_size hw
    omega

/-- Accepted native witnesses pay the corrected whole SIZE budget. Source
selection and byte widths are derived, not caller-supplied accounting premises. -/
theorem accepted_total {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (ts : List PTrie) (store : Nat→List Bytes)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values)
    (inner bytes : Bytes) (hpub : UniqueSourceBudget.preparedBytes p inner=some bytes)
    (hr : Public.RootsSized p) (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K) :
    ovhNat (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)+
      UniqueSourceCharge.size (DedupCompile.blocks p.lists w.entries)+
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store)≤8388608 := by
  obtain ⟨hb,_,_⟩:=DedupCompile.relD0a_inputs h hp hf hw
  have hb' : raw.length≤8388608 := by simpa only [ReexecV3D0.lenT_eq,witnessBytes] using hb
  obtain ⟨he,ha,ht,henc⟩:=decoded_shapes hw hb'
  exact UniqueSourceBudget.encoded_budget ts store w hs he ha ht p inner bytes hpub hr hi hk _
    (UniqueSourceNativeBudget.accepted_dictionary h hp hf hw) henc
/-- The same accepted native witness supplies receiver legality for the actual
chain-patched node/value inventory and corrected source compiler. -/
theorem accepted_receiver {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (ts : List PTrie) (store : Nat→List Bytes)
    (hs : ts.zipIdx.map (fun p=>store p.2)=(transitions w).map Transition.values)
    (ht : ∀t∈ts,t.wf=true) (hb : preBytes ts≤2000000)
    (hn : NodeWf3 (forestNodes 0 0 0 ts))
    (hst : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1)
    (inner bytes : Bytes) (hpub : UniqueSourceBudget.preparedBytes p inner=some bytes)
    (hr : Public.RootsSized p) (hi : w.innerBytes=inner) (hk : w.implicit.length=p.hdr.K) :
    let vs:=Assembly.forestNodes 0 0 0 ts
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    SizeCountReceiver.Valid (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes) (UniqueSizeComponents.view ns vals (DedupCompile.blocks p.lists w.entries)) (UniqueSizeComponents.counts ns vals) := by
  exact UniqueSizeValid.native_valid ts store ht hb hn hst _ _
    (accepted_total h hp hf hw ts store hs inner bytes hpub hr hi hk)
end ZkFormal.NearV3.Candidates.UniqueSourceNativeTotal
