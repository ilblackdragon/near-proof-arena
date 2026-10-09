import ZkFormal.NearV3.Rcpt.Candidates.SizeCountPreparedOverhead
import ZkFormal.NearV3.Assembly.DecodedWitnessShape

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Near NearSpec NearSpecV3 Assembly

private theorem entry_min (e : ProofEntry) (he : e.key.length=32) :
    44≤(ZkFormal.V3.encodeEntry e).length := by
  simp only [ZkFormal.V3.encodeEntry,List.length_append,he,encList,u64,u32,leN,
    List.length_cons,List.length_nil]
  omega

private theorem dictionary_min (es : List ProofEntry) (he : ∀ e∈es,e.key.length=32) :
    44*es.length+4≤(encList ZkFormal.V3.encodeEntry es).length := by
  have hh : 44*es.length≤(es.map fun e => (ZkFormal.V3.encodeEntry e).length).sum := by
    induction es with
    | nil => simp
    | cons e es ih =>
      have hh := entry_min e (he e (by simp))
      have ht := ih (fun x hx => he x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  simp only [encList,List.length_append,u32,leN,List.length_cons,List.length_nil,concatAll_size]
  omega

/-- The native encoded-size check already bounds the entire fixed overhead,
including arbitrary unused dictionary entries and repeated-key cardinality. -/
theorem shape_fixed_overhead (w : StateWitness) (N : Nat) (hs : ZkFormal.V3.D0Shape w)
    (hn : N≤w.entries.length) (hb : (ZkFormal.V3.encodeSW w).length≤8388608) :
    224+w.innerBytes.length+44*N+69*w.implicit.length≤8388608 := by
  simp only [ZkFormal.V3.D0Shape,ZkFormal.V3.D0Shape.wf,Bool.and_eq_true] at hs
  have he : w.epochId.length=32 := by
    have hh : ZkFormal.V3.h32 w.epochId=true := by grind only
    simpa [ZkFormal.V3.h32] using hh
  have ha : w.appliedReceiptsHash.length=32 := by
    have hh : ZkFormal.V3.h32 w.appliedReceiptsHash=true := by grind only
    simpa [ZkFormal.V3.h32] using hh
  have hm : ZkFormal.V3.transitionWf w.main=true := by grind only
  have hi : w.implicit.all ZkFormal.V3.transitionWf=true := by grind only
  have ht : ∀ t∈transitions w,t.blockHash.length=32 ∧ t.postStateRoot.length=32 := by
    intro t ht
    have hw : ZkFormal.V3.transitionWf t=true := by
      simp only [transitions,List.mem_cons] at ht
      rcases ht with rfl|ht
      · exact hm
      · exact List.all_eq_true.mp hi t ht
    simp only [ZkFormal.V3.transitionWf,Bool.and_eq_true,ZkFormal.V3.h32,beq_iff_eq] at hw
    grind only
  have hd : w.entries.all ZkFormal.V3.entryWf=true := by grind only
  have hk : ∀ e∈w.entries,e.key.length=32 := by
    intro e he
    have hh := List.all_eq_true.mp hd e he
    simp only [ZkFormal.V3.entryWf,Bool.and_eq_true,ZkFormal.V3.h32,beq_iff_eq] at hh
    grind only
  have hc := witness_encoding_charge w he ha ht
  have hdict := dictionary_min w.entries hk
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
