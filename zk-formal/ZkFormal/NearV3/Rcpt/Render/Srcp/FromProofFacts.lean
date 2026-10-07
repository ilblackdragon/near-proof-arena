import ZkFormal.NearV3.Rcpt.Render.Srcp.FromProof

namespace ZkFormal.NearV3.Render.SrcpGen
open NearSpec ZkFormal.Near

theorem proofHashStep_length (acc : Bytes) (step : Bytes × Nat) :
    (proofHashStep acc step).length = 32 := by
  unfold proofHashStep
  split <;> exact ArenaCore.sha256_length _

/-- Decoded 32-byte siblings and SHA outputs give exactly 32-byte table windows. -/
theorem proofItems_lengths (path : List (Bytes × Nat)) (q len : Nat) (acc : Bytes)
    (ha : acc.length = 32) (hp : ∀ step ∈ path, step.1.length = 32) :
    ∀ it ∈ proofItems q len acc path, it.sib.length = 32 ∧ it.acc.length = 32 := by
  induction path generalizing q len acc with
  | nil => simp [proofItems]
  | cons step rest ih =>
    intro it hit
    simp only [proofItems, List.mem_cons] at hit
    rcases hit with rfl | hit
    · simp [hp step (by simp), ha]
    · exact ih _ _ _ (proofHashStep_length _ _) (fun s hs => hp s (by simp [hs])) it hit

private theorem toBytes_map (bs : Bytes) : toBytes (bs.map UInt8.toNat) = bs := by
  simp [toBytes, List.map_map, Function.comp_def, UInt8.ofNat_toNat]

/-- Legal decoded directions round-trip exactly; the SHA accumulator is internal. -/
theorem proofItems_steps (path : List (Bytes × Nat)) (q len : Nat) (acc : Bytes)
    (hd : ∀ step ∈ path, step.2 = 0 ∨ step.2 = 1) :
    (proofItems q len acc path).map SrcpItem.proofStep = path := by
  induction path generalizing q len acc with
  | nil => rfl
  | cons step rest ih =>
    simp only [proofItems, List.map_cons, SrcpItem.proofStep, toBytes_map]
    have ht := ih (q + 1) 64 (proofHashStep acc step) (fun s hs => hd s (by simp [hs]))
    rw [ht]
    have hs := hd step (by simp)
    rcases hs with hs | hs <;> simp [hs] <;> cases step <;> simp_all

/-- The block generator preserves the spec's receipt-list bytes and input path. -/
theorem blockOfProof_leaf_path (root : Bytes) (dup : Bool) (j q : Nat) (e : NearSpecV3.ProofEntry)
    (hd : ∀ step ∈ e.proof.path, step.2 = 0 ∨ step.2 = 1) :
    toBytes (blockOfProof root dup j q e).leaf = sha256 (u64 e.proof.toShard ++ encodeReceipts e.receipts) ∧
    (blockOfProof root dup j q e).path.map SrcpItem.proofStep = e.proof.path := by
  exact ⟨toBytes_map _, proofItems_steps _ _ _ _ hd⟩

end ZkFormal.NearV3.Render.SrcpGen
