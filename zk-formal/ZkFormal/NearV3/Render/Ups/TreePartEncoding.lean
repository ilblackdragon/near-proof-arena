import ZkFormal.NearV3.Render.Ups.TreeNodeBytes
import ZkFormal.NearV3.Render.Ups.TreeTraceCorrect

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

/-- Encode the source/output tries of an actual trace part. Non-byte metadata is
supplied by the path/store allocator; the part kind is fixed by runtime dispatch. -/
def encodeTreePart (base : UpsPartI) (part : TreePart) : Option UpsPartI := do
  let src ← treeNode part.source
  let dst ← treeNode part.output
  return encodePart {base with kind := part.kind.ix} src dst

theorem encodeTreePart_kind {base Q : UpsPartI} {part : TreePart}
    (h : encodeTreePart base part=some Q) : Q.kind=part.kind.ix := by
  unfold encodeTreePart at h
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at h
  subst Q; rfl

theorem encodeTreePart_bytes {base Q : UpsPartI} {part : TreePart}
    (h : encodeTreePart base part=some Q)
    (hs : part.source.wf=true) (hd : part.output.wf=true)
      :
    Q.pb=(nodeEnc part.source).map UInt8.toNat ∧ Q.q=(nodeEnc part.output).map UInt8.toNat := by
  unfold encodeTreePart at h
  cases hsrc : treeNode part.source <;> cases hdst : treeNode part.output <;> simp [hsrc,hdst] at h
  subst Q
  exact ⟨treeNode_ser hs hsrc true,treeNode_ser hd hdst false⟩

theorem treeNode_hash {t : PTrie} {node : NodeV3} (hw : t.wf=true)
     (hn : treeNode t=some node) (post : Bool) :
    sha256 ((node.ser post).map UInt8.ofNat)=t.hashOf := by
  have hi : isNode t=true := by cases t <;> simp_all [treeNode,isNode]
  rw [treeNode_ser hw hn post,List.map_map]
  have hmap : (fun x : UInt8 => UInt8.ofNat x.toNat)=id := by funext x; exact UInt8.ofNat_toNat
  simp only [Function.comp_def] at hmap ⊢
  rw [hmap,List.map_id]
  exact (hashOf_eq_enc t hi).symm

/-- Actual upsert output hash, recovered from the executable node-view serializer. -/
theorem trace_root_hash {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun} {node : NodeV3}
    (hr : traceUpsert t key v=some run) (hw : run.output.wf=true)
     (hn : treeNode run.output=some node) :
    t.upsert key v=some run.output ∧ sha256 ((node.ser false).map UInt8.ofNat)=run.output.hashOf := by
  refine ⟨?_,treeNode_hash hw hn false⟩
  have h := traceUpsert_output t key v
  simpa [hr] using h.symm

end ZkFormal.NearV3.Render.UpsGen
