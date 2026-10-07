import ZkFormal.NearV3.Rcpt.Extract.Srcp.Defs
import ZkFormal.Near.Extract.RcptView
import NearSpecV3.ChunkValidationV0

/-!
# Source-proof digest chains implement `rootFromPath`

This semantic bridge consumes digest equalities supplied by SHA message linking.
It does not assume collision resistance or introduce a hash axiom. The remaining
assembly obligation is to obtain `SourceHashes` from bus balance and the closed
SHA-table contract, using the extracted exact traffic and id separation.
-/

namespace ZkFormal.NearV3

open ZkFormal.Near NearSpec

def SrcpItem.proofStep (it : SrcpItem) : Bytes × Nat :=
  (toBytes it.sib, if it.dir then 1 else 0)

/-- SHA equalities for the messages in one extracted source-proof block. -/
structure SourceHashes (B : SrcpB) (dig : Nat → Bytes) : Prop where
  leaf : dig B.ql = sha256 (toBytes B.leaf)
  items : ∀ it ∈ B.path,
    toBytes it.acc = dig it.pq ∧ dig it.q = sha256 (toBytes it.bytes)
  root : toBytes B.root = dig B.qe

/-- Consecutive digest messages give exactly the spec's recursive Merkle path. -/
theorem srcp_path_chain (path : List SrcpItem) (start : Nat) (dig : Nat → Bytes)
    (h : ∀ i (hi : i < path.length),
      toBytes path[i].acc = dig (start + i) ∧
      dig (start + i + 1) = sha256 (toBytes path[i].bytes)) :
    NearSpecV3.rootFromPath (dig start) (path.map SrcpItem.proofStep) =
      dig (start + path.length) := by
  induction path generalizing start with
  | nil => simp [NearSpecV3.rootFromPath]
  | cons it rest ih =>
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    rw [List.map_cons, NearSpecV3.rootFromPath]
    have hs : (if it.proofStep.2 == 0 then sha256 (it.proofStep.1 ++ dig start)
        else sha256 (dig start ++ it.proofStep.1)) = dig (start + 1) := by
      rw [← h0.1, h0.2]
      cases hd : it.dir <;> simp [SrcpItem.proofStep, SrcpItem.bytes, hd, toBytes, List.map_append]
    rw [hs, ih (start + 1)]
    · congr 1; simp only [List.length_cons]; omega
    · intro i hi
      have he := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

/-- The extracted root is the spec's root of the leaf rehash and ordered path. -/
theorem srcp_rootFromPath {bs : List SrcpB} (hw : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    (dig : Nat → Bytes) (hh : SourceHashes B dig) :
    NearSpecV3.rootFromPath (sha256 (toBytes B.leaf)) (B.path.map SrcpItem.proofStep) =
      toBytes B.root := by
  rw [← hh.leaf]
  have hc : ∀ i (hi : i < B.path.length),
      toBytes B.path[i].acc = dig (B.ql + i) ∧
      dig (B.ql + i + 1) = sha256 (toBytes B.path[i].bytes) := by
    intro i hi
    have hiw := hw.items B hB i hi
    have hih := hh.items B.path[i] (List.getElem_mem hi)
    rw [hiw.2.1] at hih
    rw [hiw.1] at hih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih
  rw [srcp_path_chain B.path B.ql dig hc]
  have hqe : B.qe = B.ql + B.path.length := (hw.root B hB).1
  rw [← hqe, hh.root]

/-- With the receipt-list digest linked, the block satisfies the actual receipt-proof verifier. -/
theorem srcp_verifyReceiptProof {bs : List SrcpB} (hw : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    (dig : Nat → Bytes) (hh : SourceHashes B dig) (e : NearSpecV3.ProofEntry)
    (hleaf : toBytes B.leaf = sha256 (u64 e.proof.toShard ++ encodeReceipts e.receipts))
    (hpath : e.proof.path = B.path.map SrcpItem.proofStep) :
    NearSpecV3.verifyReceiptProof (toBytes B.root) e = true := by
  unfold NearSpecV3.verifyReceiptProof
  dsimp only
  rw [hpath, ← hleaf, srcp_rootFromPath hw hB dig hh]
  simp

end ZkFormal.NearV3
