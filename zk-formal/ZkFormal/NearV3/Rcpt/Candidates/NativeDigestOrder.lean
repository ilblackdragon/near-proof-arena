import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestForest

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

def indexedOwners : Nat→List PTrie→List (Nat×PTrie)
  | _,[]=>[]
  | n,t::ts=>(n,t)::indexedOwners (n+1) ts

theorem indexedOwners_append (as bs : List PTrie) (n : Nat) :
    indexedOwners n (as++bs)=indexedOwners n as++indexedOwners (n+as.length) bs := by
  induction as generalizing n with
  | nil=>simp [indexedOwners]
  | cons a as ih=>
    simp only [List.cons_append,indexedOwners,ih,List.length_cons]
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

mutual
theorem occurrenceOwners_indexed : ∀(t : PTrie)(n : Nat),
    occurrenceOwners n t=indexedOwners n (occs t)
  | .hash _,_=>rfl
  | .leaf _ _ _,_=>rfl
  | .ext _ c _,n=>by simp only [occurrenceOwners,occs,indexedOwners,occurrenceOwners_indexed]
  | .branch _ cs _,n=>by simp only [occurrenceOwners,occs,indexedOwners,kidOccurrenceOwners_indexed]
theorem kidOccurrenceOwners_indexed : ∀(cs : Kids)(n : Nat),
    kidOccurrenceOwners n cs=indexedOwners n (kOccs cs)
  | .nil,_=>rfl
  | .none cs,n=>kidOccurrenceOwners_indexed cs n
  | .some c cs,n=>by simp only [kidOccurrenceOwners,kOccs,occurrenceOwners_indexed,
      kidOccurrenceOwners_indexed,indexedOwners_append]
end

theorem forestOccurrenceOwners_indexed (ts : List PTrie) (n : Nat) :
    forestOccurrenceOwners n ts=indexedOwners n (ts.flatMap occs) := by
  induction ts generalizing n with
  | nil=>rfl
  | cons t ts ih=>simp only [forestOccurrenceOwners,List.flatMap_cons,indexedOwners_append,
      occurrenceOwners_indexed,ih]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
