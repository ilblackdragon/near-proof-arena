import ZkFormal.NearV3.Rcpt.Link.SourceVerify

namespace ZkFormal.NearV3.Render.SrcpGen
open NearSpec ZkFormal.Near

/-- Hash exactly one decoded spec path step; nonzero directions select the right sibling. -/
def proofHashStep (acc : Bytes) (step : Bytes × Nat) : Bytes :=
  if step.2 == 0 then sha256 (step.1 ++ acc) else sha256 (acc ++ step.1)

/-- Compile the spec path into consecutive source-table items with honest SHA accumulators. -/
def proofItems (q len : Nat) (acc : Bytes) : List (Bytes × Nat) → List SrcpItem
  | [] => []
  | step :: rest =>
    { q := q + 1, dir := decide (step.2 ≠ 0), sib := step.1.map UInt8.toNat,
      acc := acc.map UInt8.toNat, pq := q, pl := len } ::
      proofItems (q + 1) 64 (proofHashStep acc step) rest

/-- One honest source-table block, preserving the caller's public root and duplicate flag. -/
def blockOfProof (root : Bytes) (dup : Bool) (j q : Nat) (e : NearSpecV3.ProofEntry) : SrcpB :=
  let raw := u64 e.proof.toShard ++ encodeReceipts e.receipts
  let leaf := sha256 raw
  { j := j, L := raw.length, dup := dup, root := root.map UInt8.toNat,
    qe := q + e.proof.path.length, le := if e.proof.path = [] then 32 else 64,
    ql := q, leaf := leaf.map UInt8.toNat, path := proofItems q 32 (sha256 leaf) e.proof.path }

@[simp] theorem proofItems_length (q len : Nat) (acc : Bytes) (path : List (Bytes × Nat)) :
    (proofItems q len acc path).length = path.length := by
  induction path generalizing q len acc with
  | nil => rfl
  | cons step rest ih => simp [proofItems, ih]

/-- Generated path counters match the extraction contract exactly. -/
theorem proofItems_indices (path : List (Bytes × Nat)) (q len : Nat) (acc : Bytes)
    (i : Nat) (hi : i < (proofItems q len acc path).length) :
    (proofItems q len acc path)[i].q = q + 1 + i ∧
    (proofItems q len acc path)[i].pq = q + i ∧
    (proofItems q len acc path)[i].pl = if i = 0 then len else 64 := by
  induction path generalizing q len acc i with
  | nil => simp [proofItems] at hi
  | cons step rest ih =>
    cases i with
    | zero => simp [proofItems]
    | succ i =>
      have hh := ih (q + 1) 64 (proofHashStep acc step) i (by simpa [proofItems] using hi)
      simp only [proofItems, List.getElem_cons_succ]
      obtain ⟨h1, h2, h3⟩ := hh
      refine ⟨?_, ?_, ?_⟩
      · omega
      · omega
      · simpa using h3

/-- No input byte gains a new canonicality assumption during source compilation. -/
theorem proofItems_canon (path : List (Bytes × Nat)) (q len : Nat) (acc : Bytes) :
    ∀ it ∈ proofItems q len acc path, ∀ x ∈ it.sib ++ it.acc, x < ZkFormal.Algebra.P := by
  induction path generalizing q len acc with
  | nil => simp [proofItems]
  | cons step rest ih =>
    intro it hit x hx
    simp only [proofItems, List.mem_cons] at hit
    rcases hit with rfl | hit
    · simp only [List.mem_append, List.mem_map] at hx
      rcases hx with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;>
        exact Nat.lt_trans (UInt8.toNat_lt b) (by decide)
    · exact ih (q + 1) 64 (proofHashStep acc step) it hit x hx

end ZkFormal.NearV3.Render.SrcpGen
