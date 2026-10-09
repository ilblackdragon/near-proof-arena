import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedChildIds
import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteValueIndex

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

theorem write_isNode {a b : PTrie} (h : WriteTreePair a b) : isNode a=isNode b := by
  cases h <;> rfl

/-- Skipping arbitrarily many empty extensions reaches the same global node
ID before and after receipt writes; no short-path premise is introduced. -/
theorem write_viewTarget : ∀(n : Nat){a b : PTrie},WriteTreePair a b→
    viewTarget n a=viewTarget n b
  | _,_,_,.hash _=>rfl
  | _,_,_,.leaf _ _ _=>rfl
  | n,_,_,.ext k m h=>by
    cases k with
    | nil=>simp only [viewTarget,write_isNode h];split <;> first | exact write_viewTarget (n+1) h | rfl
    | cons _ _=>rfl
  | _,_,_,.branch _ _ _=>rfl

/-- Exactly the child identity/type data observed by EDGE/BMAP. -/
def providerKid (k : NKid) : NKid := match k with
  | .none=>.none
  | .hash _=>.hash []
  | .node c _ r _ _=>.node c 0 r [] []

theorem write_providerKid (n : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    providerKid (viewKid n a)=providerKid (viewKid n b) := by
  simp only [viewKid,write_isNode h]
  split
  · simp only [providerKid,write_viewTarget n h]
  · rfl

theorem write_providerKids : ∀(n : Nat){a b : Kids},WriteKidsPair a b→
    (viewKids n a).map providerKid=(viewKids n b).map providerKid
  | _,_,_,.nil=>rfl
  | n,_,_,.none h=>by simpa only [viewKids,List.map_cons,providerKid] using congrArg (List.cons NKid.none) (write_providerKids n h)
  | n,_,_,.some h hs=>by
    simp only [viewKids,List.map_cons,write_providerKid n h,write_tsize h]
    rw [write_providerKids _ hs]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
