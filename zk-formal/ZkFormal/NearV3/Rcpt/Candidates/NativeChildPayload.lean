import ZkFormal.NearV3.Rcpt.Candidates.NativeValuePayload

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- Exact post-node occurrence bytes at their allocated global offsets. -/
def ChildPayloads (u : Inputs) (n : Nat) (ts : List PTrie) : Prop :=
  ∀i t,ts[i]?=some t→u.child (n+i)=nodeEnc t

theorem ChildPayloads.left {u : Inputs} {n : Nat} {as bs : List PTrie}
    (h : ChildPayloads u n (as++bs)) : ChildPayloads u n as := by
  intro i t hi
  apply h i t
  have hl : i<as.length := (List.getElem?_eq_some_iff.mp hi).1
  simpa only [List.getElem?_append,hl,↓reduceIte] using hi

theorem ChildPayloads.right {u : Inputs} {n : Nat} {as bs : List PTrie}
    (h : ChildPayloads u n (as++bs)) : ChildPayloads u (n+as.length) bs := by
  intro i t hi
  have hh:=h (as.length+i) t (by simp [List.getElem?_append,hi])
  simpa only [Nat.add_assoc] using hh

theorem ChildPayloads.tail {u : Inputs} {n : Nat} {a : PTrie} {as : List PTrie}
    (h : ChildPayloads u n (a::as)) : ChildPayloads u (n+1) as := by
  intro i t hi
  have hh:=h (i+1) t hi
  simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hh

/-- A child's concrete occurrence supplies its post hash; hash-only children
stay unchanged under the actual native write relation. -/
theorem kid_payload_post (u : Inputs) (n : Nat) {a b : PTrie} (hp : WriteTreePair a b)
    (h : ChildPayloads u n (occs b)) :
    (kid u (viewKid n a)).bytes true=b.hashOf.map UInt8.toNat := by
  cases hp with
  | hash hh=>rfl
  | leaf k m hs=>
    exact native_child_post u n _ _ rfl rfl (by simpa using h 0 _ rfl)
  | ext k m hc=>
    exact native_child_post u n _ _ rfl rfl (by simpa using h 0 _ rfl)
  | branch m hv hcs=>
    exact native_child_post u n _ _ rfl rfl (by simpa using h 0 _ rfl)

/-- Every branch child hash window uses the matching retained post subtree,
with offsets determined by the original preorder allocation. -/
theorem kids_payload_post : ∀(u : Inputs)(n : Nat){a b : Kids},WriteKidsPair a b→
    ChildPayloads u n (kOccs b)→
    ((viewKids n a).map (kid u)).flatMap (NKid.bytes true)=(Kids.hashes b).map UInt8.toNat
  | u,n,_,_,.nil,h=>rfl
  | u,n,_,_,.none hp,h=>by
      simpa [viewKids,NKid.bytes,kid,Kids.hashes] using kids_payload_post u n hp h
  | u,n,_,_,.some hp hs,h=>by
      have hc : ChildPayloads u n (occs _) := ChildPayloads.left h
      have hr:=ChildPayloads.right h
      have hlen : (occs _).length=tsize _ := (paired_occurrences hp).length.symm
      rw [hlen] at hr
      simp only [viewKids,List.map_cons,List.flatMap_cons,kid_payload_post u n hp hc,
        kids_payload_post u _ hs hr,Kids.hashes,List.map_append]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
