import ZkFormal.NearV3.Candidates.NativeNodeLocal
import ZkFormal.NearV3.Assembly.NativeTrace
import ZkFormal.NearV3.Assembly.NativeUnfold
namespace ZkFormal.NearV3.Candidates.NativeExecutionNodeLocal
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates.NodePostUpdate

theorem depth {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∀t∈m.pre::steps.map ImplicitStepV3.pre,∀key,fdepth t key≤trieFuel := by
  intro t ht key
  rcases List.mem_cons.mp ht with rfl|ht
  · rw [hm.pre]
    exact (built_spec _ trieFuel _ _ hm.root_length).2.2.2 key
  · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
    obtain ⟨he,hr,_⟩:=hv.input_facts s hs
    rw [he]
    exact (built_spec _ trieFuel _ _ hr).2.2.2 key

theorem nonempty {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hm : m.NativeValid k w) (ts : List PTrie) :
    0<((m.pre::ts).flatMap occs).length := by
  obtain ⟨_,_,v,_,_,hf⟩:=Qv.applyNewChunk_queue_reads hm.run
  have hh : m.pre.find keyDelayedIdx≠none := by rw [hf.1];simp
  cases he : m.pre with
  | hash h => simp [he,PTrie.find] at hh
  | leaf k s mem => simp [List.flatMap_cons,occs]
  | ext k c mem => simp [List.flatMap_cons,occs]
  | branch s cs mem => simp [List.flatMap_cons,occs]
/-- Successful native D0a execution constructs locally valid count-extended
node/value tables, with all forest prerequisites discharged by execution. -/
theorem complete {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (h : checkD0a B cb wb=.ok ()) (hB : B≤2000000)
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (t : Nat) (pub : List ZkFormal.Algebra.Fp) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let vs:=initializeList 0 (forestNodes 0 0 0 ts)
    let es:=seedValuesFrom 0 (forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    TableLocal Rcpt.Candidates.SizeCount.nodeTable
      (TrieCountHeight.node (ChainMetadata.assign cs 0 vs) pub) t pub ∧
    TableLocal Rcpt.Candidates.SizeCount.valTable
      (TrieCountHeight.value (ChainMetadata.assignValues cs es) pub) t pub := by
  have hc : checkD0 cb wb=.ok () := by
    have hh:=((relD0a_iff B cb wb).mpr h).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hc
  apply NativeNodeLocal.complete _ _ (Nat.le_trans (checkD0a_preBytes hk hw h hm hv) hB)
    (depth hm hv) _ (nonempty hm _) t pub
  · intro tr hr
    rcases List.mem_cons.mp hr with rfl|hr
    · rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hr
      exact (hv.input_facts s hs).2.2
  · have hs:=hv.length
    simp only [List.length_zip] at hs
    change (steps.map ImplicitStepV3.pre).length+1≤2013265921
    simp only [List.length_map]
    omega

end ZkFormal.NearV3.Candidates.NativeExecutionNodeLocal
