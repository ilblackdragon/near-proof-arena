import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestTree

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

def forestRootOwners : Nat→List PTrie→List (Nat×PTrie)
  | _,[]=>[]
  | n,t::ts=>rootOwner n t++forestRootOwners (n+tsize t) ts

def forestOccurrenceOwners : Nat→List PTrie→List (Nat×PTrie)
  | _,[]=>[]
  | n,t::ts=>occurrenceOwners n t++forestOccurrenceOwners (n+tsize t) ts

private theorem append_interleave {α : Type} (a b c d : List α) :
    (a++b++(c++d)).Perm (a++c++(b++d)) := by
  simpa only [List.append_assoc] using (List.Perm.append_left a
    (List.Perm.append_right d (List.perm_append_comm (l₁:=b) (l₂:=c))))

/-- All concrete updated forest records, with global node/value offsets. -/
theorem forest_digest_partition (u : Inputs) : ∀(ts : List PTrie)(tau n v : Nat),
    ((forestRootOwners n ts).flatMap (ownerDigests u)++
      (records u (forestNodes tau n v ts)).flatMap childDigests).Perm
      ((forestOccurrenceOwners n ts).flatMap (ownerDigests u))
  | [],_,_,_=>by simp [forestRootOwners,forestOccurrenceOwners,forestNodes,records]
  | t::ts,tau,n,v=>by
    simp only [forestRootOwners,forestOccurrenceOwners,forestNodes,records,List.map_append,List.flatMap_append]
    exact (append_interleave _ _ _ _).trans
      ((tree_digest_partition u t tau 0 n v).append
        (forest_digest_partition u ts (tau+1) (n+tsize t) (v+(valsOf t).length)))

/-- Payload projection preserves duplicate occurrence multiplicity in the exact
forest ownership permutation. -/
theorem forest_digest_counts (u : Inputs) (ts : List PTrie) (tau n v : Nat)
    (msg : Msg) :
    ((forestRootOwners n ts).flatMap (ownerDigests u)).count msg+
      ((records u (forestNodes tau n v ts)).flatMap childDigests).count msg=
      ((forestOccurrenceOwners n ts).flatMap (ownerDigests u)).count msg := by
  simpa only [List.count_append] using (forest_digest_partition u ts tau n v).count_eq msg

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
