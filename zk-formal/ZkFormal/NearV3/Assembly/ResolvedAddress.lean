import ZkFormal.NearV3.Assembly.PartAddress
import ZkFormal.NearV3.Render.Ups.TreeResolvePath

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

/-- Resolve empty extensions while retaining the actual occurrence offsets. -/
def resolveAddress : Nat → Nat → Nat → PTrie → OccurrenceAddress
  | n,v,d,.ext [] c _ => resolveAddress (n+1) v (d+1) c
  | n,v,d,t => ⟨n,v,d,t⟩

theorem resolveAddress_tree : ∀ n v d t,
    (resolveAddress n v d t).tree=resolveNative t
  | _,_,_,.hash _ => rfl
  | _,_,_,.leaf .. => rfl
  | n,v,d,.ext [] c _ => resolveAddress_tree (n+1) v (d+1) c
  | _,_,_,.ext (_::_) _ _ => rfl
  | _,_,_,.branch .. => rfl

theorem resolveAddress_segment {L VL D tau} : ∀ n v d t,
    Seg L VL D tau n v d t →
    let a := resolveAddress n v d t
    Seg L VL D tau a.nid a.vid a.depth a.tree
  | _,_,_,.hash _,h => h
  | _,_,_,.leaf ..,h => h
  | n,v,d,.ext [] c _,h => resolveAddress_segment (n+1) v (d+1) c h.ext_kid
  | _,_,_,.ext (_::_) _ _,h => h
  | _,_,_,.branch ..,h => h

/-- The concrete node view's resolved target is exactly the allocated resolved
occurrence whenever that target is revealed. -/
theorem resolveAddress_target : ∀ n v d t,
    isNode (resolveNative t)=true → (resolveAddress n v d t).nid=viewTarget n t
  | _,_,_,.hash _,h => by simp [resolveNative,isNode] at h
  | _,_,_,.leaf ..,_ => rfl
  | n,v,d,.ext [] c m,h => by
    have hc : isNode c=true := by cases c <;> simp_all [resolveNative,isNode]
    simp only [resolveAddress,viewTarget,hc,ite_true]
    exact resolveAddress_target (n+1) v (d+1) c h
  | _,_,_,.ext (_::_) _ _,_ => rfl
  | _,_,_,.branch ..,_ => rfl

/-- Empty extension resolution preserves the actual native lookup. -/
theorem resolveNative_find : ∀ t key, (resolveNative t).find key=t.find key
  | .hash _,_ => rfl
  | .leaf ..,_ => rfl
  | .ext [] c _,key => by simpa [resolveNative,PTrie.find,isPrefix] using resolveNative_find c key
  | .ext (_::_) _ _,_ => rfl
  | .branch ..,_ => rfl

theorem resolveNative_isNode_of_known {t : PTrie} {key : List Nat}
    (h : t.find key≠none) : isNode (resolveNative t)=true := by
  have hk : (resolveNative t).find key≠none := by rwa [resolveNative_find]
  cases ht : resolveNative t <;> simp_all [isNode,PTrie.find]

end ZkFormal.NearV3.Assembly
