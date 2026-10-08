import ZkFormal.NearV3.Rcpt.Candidates.NativeForestAllocation

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- Root occurrence ownership is conditional on revelation; hashed stubs are not nodes. -/
def rootOwner (n : Nat) (t : PTrie) : List (Nat×PTrie) :=
  if isNode t then [(n,t)] else []

mutual
def occurrenceOwners (n : Nat) : PTrie→List (Nat×PTrie)
  | .hash _=>[]
  | t@(.leaf _ _ _)=>[(n,t)]
  | t@(.ext _ c _)=>(n,t)::occurrenceOwners (n+1) c
  | t@(.branch _ cs _)=>(n,t)::kidOccurrenceOwners (n+1) cs
def kidOccurrenceOwners (n : Nat) : Kids→List (Nat×PTrie)
  | .nil=>[]
  | .none cs=>kidOccurrenceOwners n cs
  | .some c cs=>occurrenceOwners n c++kidOccurrenceOwners (n+tsize c) cs
end

def kidRootOwners : Nat→Kids→List (Nat×PTrie)
  | _,.nil=>[]
  | n,.none cs=>kidRootOwners n cs
  | n,.some c cs=>rootOwner n c++kidRootOwners (n+tsize c) cs

mutual
def parentOwners (n : Nat) : PTrie→List (Nat×PTrie)
  | .hash _=>[]
  | .leaf _ _ _=>[]
  | .ext _ c _=>rootOwner (n+1) c++parentOwners (n+1) c
  | .branch _ cs _=>kidRootOwners (n+1) cs++kidParentOwners (n+1) cs
def kidParentOwners (n : Nat) : Kids→List (Nat×PTrie)
  | .nil=>[]
  | .none cs=>kidParentOwners n cs
  | .some c cs=>parentOwners n c++kidParentOwners (n+tsize c) cs
end

private theorem append_interleave {α : Type} (a b c d : List α) :
    (a++b++(c++d)).Perm (a++c++(b++d)) := by
  simpa only [List.append_assoc] using (List.Perm.append_left a
    (List.Perm.append_right d (List.perm_append_comm (l₁:=b) (l₂:=c))))

mutual
/-- Every revealed node is owned exactly once by a root or its revealed parent.
Repeated equal subtrees retain their distinct preorder IDs and multiplicities. -/
theorem tree_digest_ownership : ∀(t : PTrie)(n : Nat),
    (rootOwner n t++parentOwners n t).Perm (occurrenceOwners n t)
  | .hash _,n=>by simp [rootOwner,isNode,parentOwners,occurrenceOwners]
  | .leaf k v m,n=>by simp [rootOwner,isNode,parentOwners,occurrenceOwners]
  | .ext k c m,n=>by
    simpa only [rootOwner,isNode,ite_true,List.singleton_append,parentOwners,occurrenceOwners] using
      (tree_digest_ownership c (n+1)).cons (n,.ext k c m)
  | .branch v cs m,n=>by
    simpa only [rootOwner,isNode,ite_true,List.singleton_append,parentOwners,occurrenceOwners] using
      (kids_digest_ownership cs (n+1)).cons (n,.branch v cs m)
theorem kids_digest_ownership : ∀(cs : Kids)(n : Nat),
    (kidRootOwners n cs++kidParentOwners n cs).Perm (kidOccurrenceOwners n cs)
  | .nil,n=>by simp [kidRootOwners,kidParentOwners,kidOccurrenceOwners]
  | .none cs,n=>kids_digest_ownership cs n
  | .some c cs,n=>by
    simp only [kidRootOwners,kidParentOwners,kidOccurrenceOwners]
    exact (append_interleave _ _ _ _).trans
      ((tree_digest_ownership c n).append (kids_digest_ownership cs (n+tsize c)))
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
