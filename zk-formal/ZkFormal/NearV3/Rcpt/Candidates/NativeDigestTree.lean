import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestRequests

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

mutual
theorem seed_parent_digests (u : Inputs) : ∀(t : PTrie)(tau d n v : Nat),
    (records u (seedNodesT tau d n v t)).flatMap childDigests=
      (parentOwners n t).flatMap (ownerDigests u)
  | .hash _,_,_,_,_=>rfl
  | .leaf k sl m,tau,d,n,v=>by
    simp only [seedNodesT,records,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,
      seed_child_digests,parentOwners,List.flatMap_nil,List.nil_append]
  | .ext k c m,tau,d,n,v=>by
    simp only [seedNodesT,records,List.map_cons,List.flatMap_cons,seed_child_digests,parentOwners,
      List.flatMap_append]
    rw [←seed_parent_digests u c tau (d+1) (n+1) v]
    rfl
  | .branch sl cs m,tau,d,n,v=>by
    simp only [seedNodesT,records,List.map_cons,List.flatMap_cons,seed_child_digests,parentOwners,
      List.flatMap_append]
    rw [←seed_kid_parent_digests u cs tau (d+1) (n+1) (v+(optSlotVal sl).length)]
    rfl
theorem seed_kid_parent_digests (u : Inputs) : ∀(cs : Kids)(tau d n v : Nat),
    (records u (seedKidsT tau d n v cs)).flatMap childDigests=
      (kidParentOwners n cs).flatMap (ownerDigests u)
  | .nil,_,_,_,_=>rfl
  | .none cs,tau,d,n,v=>seed_kid_parent_digests u cs tau d n v
  | .some c cs,tau,d,n,v=>by
    simp only [seedKidsT,records,List.map_append,List.flatMap_append,kidParentOwners]
    rw [←seed_parent_digests u c tau d n v,
      ←seed_kid_parent_digests u cs tau d (n+tsize c) (v+(valsOf c).length)]
    rfl
end

/-- Exact multiplicity partition for actual updated seed-record child requests.
Only the root term is conditional on the native root being revealed. -/
theorem tree_digest_partition (u : Inputs) (t : PTrie) (tau d n v : Nat) :
    ((rootOwner n t).flatMap (ownerDigests u)++
      (records u (seedNodesT tau d n v t)).flatMap childDigests).Perm
      ((occurrenceOwners n t).flatMap (ownerDigests u)) := by
  rw [seed_parent_digests,←List.flatMap_append]
  exact (tree_digest_ownership t n).flatMap_right _

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
