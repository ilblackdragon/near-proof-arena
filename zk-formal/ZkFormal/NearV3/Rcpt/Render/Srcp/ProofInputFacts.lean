import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofInputs

namespace ZkFormal.NearV3.Render.SrcpGen
open NearSpec ZkFormal.Near

@[simp] theorem blocksOfProofs_length (xs : List ProofInput) : (blocksOfProofs xs).length = xs.length := by
  simp [blocksOfProofs]

theorem blocksOfProofs_get (xs : List ProofInput) (i : Nat) (hi : i < (blocksOfProofs xs).length) :
    (blocksOfProofs xs)[i] =
      blockOfProof (xs[i]'(by simpa using hi)).root (xs[i]'(by simpa using hi)).dup i (1 + proofWeight (xs.take i)) (xs[i]'(by simpa using hi)).entry := by
  simp [blocksOfProofs]

private theorem take_next {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using congrArg (List.cons a) (ih i (by simpa using hi))

theorem proofWeight_next (xs : List ProofInput) (i : Nat) (hi : i < xs.length) :
    proofWeight (xs.take (i + 1)) = proofWeight (xs.take i) + 1 + xs[i].entry.proof.path.length := by
  rw [take_next xs i hi]
  simp only [proofWeight, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem blockOfProof_items (root : Bytes) (dup : Bool) (j q : Nat) (e : NearSpecV3.ProofEntry)
    (i : Nat) (hi : i < (blockOfProof root dup j q e).path.length) :
    (blockOfProof root dup j q e).path[i].q = q + 1 + i ∧
    (blockOfProof root dup j q e).path[i].pq = q + i ∧
    (blockOfProof root dup j q e).path[i].pl = if i = 0 then 32 else 64 :=
  proofItems_indices _ _ _ _ i hi

theorem blockOfProof_root (root : Bytes) (dup : Bool) (j q : Nat) (e : NearSpecV3.ProofEntry) :
    (blockOfProof root dup j q e).qe = (blockOfProof root dup j q e).lastQ ∧
    (blockOfProof root dup j q e).le = if (blockOfProof root dup j q e).path = [] then 32 else 64 := by
  constructor
  · simp [blockOfProof, SrcpB.lastQ]
  · have hn : proofItems q 32 (sha256 (sha256 (u64 e.proof.toShard ++ encodeReceipts e.receipts))) e.proof.path = [] ↔
        e.proof.path = [] := by
      rw [← List.length_eq_zero_iff, proofItems_length, List.length_eq_zero_iff]
    simp only [blockOfProof, hn]

end ZkFormal.NearV3.Render.SrcpGen
