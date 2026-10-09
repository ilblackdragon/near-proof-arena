import ZkFormal.NearV3.Assembly.CompactLeafDigestInventory
import ZkFormal.NearV3.Assembly.CompactExtensionDigestInventory
import ZkFormal.NearV3.Assembly.CompactDigestTargets

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

/-- RLP and NLF consume fresh value job0 exactly once, after their full header. -/
theorem fresh_leaf_target (I : Render.UpsInst) (k : Nat) (hf : FieldsOk (part I k))
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=2∨(part I k).kind=8) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k (9+(part I k).qhk) 0 (L I)] := by
  rw [leaf_digest_inventory I k hf (hp.tyLeaf (by omega)),value_field_target]
  rcases hk with hk|hk <;> simp [VcpB,hk]

/-- MVL copies its old value digest and introduces no lookup. -/
theorem moved_leaf_no_digest (I : Render.UpsInst) (k : Nat) (hf : FieldsOk (part I k))
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=6) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=[] := by
  rw [leaf_digest_inventory I k hf (hp.tyLeaf (by omega)),value_field_target]
  simp [VcpB,hk]

/-- RDE, WEX and PT consume the preceding output job at their exact child
window, with the allocator's checked native child length. -/
theorem extension_child_target (I : Render.UpsInst) (k : Nat) (hf : FieldsOk (part I k))
    (hp : PartOk I k (part I k))
    (hk : (part I k).kind=1∨(part I k).kind=9∨(part I k).kind=11) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      [digestWindow I k (5+(part I k).qhk) k (part I k).clen] := by
  rw [extension_digest_inventory I k hf (hp.tyExt (by omega)),child_field_target]
  have hj:=(hp.jmD (by omega))
  rcases hk with hk|hk|hk <;> simp [WfrB,WnB,hk,hj]

/-- MVE copies its existing child digest and introduces no lookup. -/
theorem moved_extension_no_digest (I : Render.UpsInst) (k : Nat) (hf : FieldsOk (part I k))
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=7) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=[] := by
  rw [extension_digest_inventory I k hf (hp.tyExt (by omega)),child_field_target]
  simp [WfrB,hk]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
