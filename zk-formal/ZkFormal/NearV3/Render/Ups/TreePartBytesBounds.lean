import ZkFormal.NearV3.Render.Ups.TreePartEncoding

namespace ZkFormal.NearV3.Render.UpsGen

theorem encoded_source_byte_bounds {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) (hw : part.source.wf=true) :
    ∀ b∈Q.pb,b<256 := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at he
  subst Q
  exact treeNode_byte_bound hw hs true
end ZkFormal.NearV3.Render.UpsGen
