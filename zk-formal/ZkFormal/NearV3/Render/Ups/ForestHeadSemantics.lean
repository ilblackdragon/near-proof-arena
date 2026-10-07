import ZkFormal.NearV3.Render.Ups.ForestWalkHeads

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 Assembly

/-- Filling root walk targets preserves the native post-root selected by instance. -/
theorem forestWalkHeads_post_lookup : ∀ tau n pairs target,
    ((forestWalkHeads tau n pairs).find? (fun h=>h.tau==target)).map HeadE.post=
      ((traceHeads tau n pairs).find? (fun h=>h.tau==target)).map HeadE.post
  | _,_,[],_ => rfl
  | tau,n,(pre,post)::rest,target => by
    simp only [forestWalkHeads,traceHeads,List.find?_cons]
    split
    · rfl
    · exact forestWalkHeads_post_lookup (tau+1) (n+tsize pre) rest target

/-- Concrete runtime views with resolved START providers; store bytes and post roots
are identical to the already constructed native execution views. -/
def walkStoreViews (pairs : List (PTrie×PTrie)) : ExtV3 :=
  {traceStoreViews pairs with heads:=forestWalkHeads 0 0 pairs}

theorem walkStoreViews_store (pairs : List (PTrie×PTrie)) (tau : Nat) :
    (walkStoreViews pairs).store tau=(traceStoreViews pairs).store tau := rfl

theorem walkStoreViews_post (pairs : List (PTrie×PTrie)) (tau : Nat) :
    (walkStoreViews pairs).post tau=(traceStoreViews pairs).post tau := by
  unfold ExtV3.post walkStoreViews traceStoreViews
  rw [forestWalkHeads_post_lookup]

/-- Every actual native transition's post digest is retained after START resolution. -/
theorem walkStoreViews_native_post {pairs : List (PTrie×PTrie)} {i : Nat} {pair : PTrie×PTrie}
    (hp : pairs[i]?=some pair) : (walkStoreViews pairs).post i=pair.2.hashOf := by
  rw [walkStoreViews_post]
  exact traceStoreViews_post hp
end ZkFormal.NearV3.Render.UpsGen
