import ZkFormal.NearV3.Render.Ups.NativePartInputs
import ZkFormal.NearV3.Render.Node.HeaderBounds

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

/-- Prefix lengths are bounded by actual serialized payload lengths. No small-key
assumption is introduced, and output memory need not satisfy full trie wf. -/
theorem encodeTreePart_prefix_lengths {base Q : UpsPartI} {p : TreePart}
    (he : encodeTreePart base p=some Q) (hw : p.source.wf=true) :
    Q.qhk≤Q.q.length ∧ Q.phk≤Q.pb.length := by
  unfold encodeTreePart at he
  cases hs : treeNode p.source <;> cases hd : treeNode p.output <;> simp [hs,hd] at he
  rename_i src dst
  subst Q
  have hsw := treeNode_wf hw hs
  constructor
  · exact NodeGen3.hplen_le_ser dst
  · change NodeGen3.hplenOf src≤(src.ser true).length
    rw [NodeGen3.ser_len hsw true,←NodeGen3.ser_len hsw false]
    exact NodeGen3.hplen_le_ser src

/-- Final signed instances retain these source and output serialization bounds. -/
theorem nativeInstance_prefix_lengths (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] value=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    let Q := part (nativeInstance recordId baseI root run value Qs) k
    Q.qhk≤Q.q.length ∧ Q.phk≤Q.pb.length := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  have hsource := (traceUpsert_sources root [0,15] value run hw hr).2 p (List.mem_of_getElem? hp)
  dsimp only
  rw [hpart]
  change Q.qhk≤Q.q.length ∧ Q.phk≤Q.pb.length
  exact encodeTreePart_prefix_lengths henc hsource

/-- Prefix bounds expressed against actual native serialized source/output
payloads, ready for the accepted scheduler's aggregate byte accounting. -/
theorem nativeInstance_prefix_nativeLengths (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] value=some run)
    (hw : root.wf=true) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs) (k : Nat) (hk : k<Qs.length) :
    ∃ p,run.parts[k]?=some p ∧
      (part (nativeInstance recordId baseI root run value Qs) k).qhk≤(nodeEnc p.output).length ∧
      (part (nativeInstance recordId baseI root run value Qs) k).phk≤(nodeEnc p.source).length := by
  obtain ⟨p,Q,hp,hQ,henc,hpart⟩ := nativeInstance_part recordId baseI hr base he k hk
  have hsource := (traceUpsert_sources root [0,15] value run hw hr).2 p (List.mem_of_getElem? hp)
  have hb := encodeTreePart_prefix_lengths henc hsource
  have hs := congrArg List.length (Assembly.encodeTreePart_native_bytes henc).1
  have ho := congrArg List.length (Assembly.encodeTreePart_native_bytes henc).2
  simp only [List.length_map] at hs ho
  refine ⟨p,hp,?_,?_⟩ <;> rw [hpart]
  · change Q.qhk≤(nodeEnc p.output).length
    exact ho ▸ hb.1
  · change Q.phk≤(nodeEnc p.source).length
    exact hs ▸ hb.2
end ZkFormal.NearV3.Render.UpsGen
