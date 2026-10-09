import ZkFormal.NearV3.Candidates.OriginalSourceNativeTotal
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountAcceptedOverhead
import ZkFormal.NearV3.Assembly.PrepFacts
namespace ZkFormal.NearV3.Candidates.NativeSizeConstruction
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates

/-- Actual accepted input fixes the original public bytes, inner bytes and K.
These are derived from native execution, not independent accounting premises. -/
theorem public_fields {budget : Nat} {cb wb : Bytes} {w : StateWitness}
    {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hw : decodeW wb=.ok w) (hk : walkD0 cb=.ok k) :
    SizeCount.countedPreparedBytes p k.c.chunkInner=
      some (Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)) ∧
    Public.RootsSized p ∧ w.innerBytes=k.c.chunkInner ∧ w.implicit.length=p.hdr.K := by
  have hc : checkD0 cb wb=.ok () := by
    have hh:=h.1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,_,hi,_⟩:=checkD0_witness_fields hk hw hc
  obtain ⟨_,_,_,_,hK,_⟩:=checkD0_native_steps hk hw hc
  refine ⟨SizeCount.accepted_counted_prepared hp hk hw hc,?_,hi,?_⟩
  · exact prepD0_roots hp
  · exact hK.trans (prepD0_implicit_count hp hk).symm

/-- Original source accounting and canonical public bytes are paid by the same
accepted witness and its actual indexed transition stores. -/
theorem total {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (ts : List PTrie) (hl : ts.length=(transitions w).length) :
    let store:=fun i=>(((transitions w)[i]?).map Transition.values).getD []
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    ovhNat (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)+
      DedupRender.size (DedupCompile.blocks p.lists w.entries)+
      HonestStoreRepresentatives.charge (NativeStoreRepresentatives.originals ts store)≤8388608 := by
  have hd : decodeW wb=.ok w := by
    unfold decodeW
    rw [hf]
    change decodeStateWitness raw=.ok w
    exact hw
  obtain ⟨hpub,hr,hi,hK⟩:=public_fields h hp hd hk
  exact OriginalSourceNativeTotal.accepted_total h hp hf hw hk ts _
    (NativeEncodedBudget.store_alignment ts w hl) _ _ hpub hr hi hK
/-- Receiver legality for the actual indexed native store and original public
constructor. Remaining hypotheses describe forest provenance and local shape. -/
theorem receiver {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (ts : List PTrie) (hl : ts.length=(transitions w).length)
    (ht : ∀t∈ts,t.wf=true) (hb : preBytes ts≤2000000)
    (hn : NodeWf3 (forestNodes 0 0 0 ts))
    (hst : ∀p∈ts.zipIdx,Stored
      (mkStore ((((transitions w)[p.2]?).map Transition.values).getD [])) p.1) :
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    let vs:=Assembly.forestNodes 0 0 0 ts
    let es:=Render.UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=ChainMetadata.assign cs 0 vs
    let vals:=ChainMetadata.assignValues cs es
    SizeCountReceiver.Valid (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp bytes)
      (SizeComponents.view ns vals (DedupCompile.blocks p.lists w.entries)) (SizeComponents.counts ns vals) := by
  exact SizeChargeFields.native_valid ts _ ht hb hn hst _ _ (total h hp hf hw hk ts hl)

/-- Generated SIZE trace has local AIR satisfaction and exact traffic for the native constructor. -/
theorem local_complete {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hk : walkD0 cb=.ok k) (ts : List PTrie) (hl : ts.length=(transitions w).length)
    (ht : ∀t∈ts,t.wf=true) (hb : preBytes ts≤2000000)
    (hn : NodeWf3 (forestNodes 0 0 0 ts))
    (hst : ∀p∈ts.zipIdx,Stored
      (mkStore ((((transitions w)[p.2]?).map Transition.values).getD [])) p.1) (t : Nat) :
    let bytes:=Public.preparedBytes p (SizeCount.fixedOverhead p k.c.chunkInner)
    let vs:=Assembly.forestNodes 0 0 0 ts
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
  exact SizeComponents.receiver_complete _ _ _ _ (receiver h hp hf hw hk ts hl ht hb hn hst) t

end ZkFormal.NearV3.Candidates.NativeSizeConstruction
