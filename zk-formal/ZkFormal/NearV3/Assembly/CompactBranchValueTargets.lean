import ZkFormal.NearV3.Assembly.CompactUnaryDigestTargets

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- RBR/RBV consume job0 once and copy every preexisting child hash. All branch
child windows remain in the scan; their DIGEST gates are proved zero. -/
theorem branch_value_target (I : Render.UpsInst) (k : Nat) (hf : FieldsOk (part I k))
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=3∨(part I k).kind=4) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k 5 0 (L I)] := by
  rw [value_branch_digest_inventory I k hf (hp.tyBV hk),value_field_target]
  rcases hk with hk|hk <;>
    simp [child_field_target,WfrB,VcpB,hk]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
