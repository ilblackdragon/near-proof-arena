import ZkFormal.NearV3.Rcpt.Link.SourceHashes

namespace ZkFormal.NearV3
open ZkFormal.Near ZkFormal.Algebra NearSpec

/-- A source block satisfying the actual SHA bus contracts computes the spec Merkle root. -/
theorem source_rootFromPath_of_sha {bs : List SrcpB} (h : SrcpWf bs)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt ((srcpTraffic bs).sends B_BYTES ++ others) m)
    (hother : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_SRC)
    (hdigest : ∀ m ∈ (srcpTraffic bs).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    {B : SrcpB} (hB : B ∈ bs) :
    NearSpecV3.rootFromPath (sha256 (toBytes B.leaf)) (B.path.map SrcpItem.proofStep) =
      toBytes B.root :=
  srcp_rootFromPath h hB (sourceDigest bs)
    (source_hashes_of_sha h hsha others hbytes hother hdigest hB)

/-- Source traffic and the receipt-list digest linkage imply the actual spec verifier. -/
theorem source_verifyReceiptProof_of_sha {bs : List SrcpB} (h : SrcpWf bs)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt ((srcpTraffic bs).sends B_BYTES ++ others) m)
    (hother : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_SRC)
    (hdigest : ∀ m ∈ (srcpTraffic bs).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    {B : SrcpB} (hB : B ∈ bs) (e : NearSpecV3.ProofEntry)
    (hleaf : toBytes B.leaf = sha256 (u64 e.proof.toShard ++ encodeReceipts e.receipts))
    (hpath : e.proof.path = B.path.map SrcpItem.proofStep) :
    NearSpecV3.verifyReceiptProof (toBytes B.root) e = true :=
  srcp_verifyReceiptProof h hB (sourceDigest bs)
    (source_hashes_of_sha h hsha others hbytes hother hdigest hB) e hleaf hpath

/-- One selected proof entry cannot verify against two different source roots.
Repeated source keys use the same `lookupLast` result, so no hash-injectivity assumption
is needed to establish their public-root consistency. -/
theorem source_roots_eq_of_same_proof (e : NearSpecV3.ProofEntry) (r s : Bytes)
    (hr : NearSpecV3.verifyReceiptProof r e = true)
    (hs : NearSpecV3.verifyReceiptProof s e = true) : r = s := by
  simp only [NearSpecV3.verifyReceiptProof, beq_iff_eq] at hr hs
  exact hr.symm.trans hs

/-- Equal source keys select the identical last-wins witness proof and hence the same root. -/
theorem source_roots_eq_of_lookupLast (entries : List NearSpecV3.ProofEntry)
    (key key' r s : Bytes) (heq : key = key')
    (e e' : NearSpecV3.ProofEntry)
    (he : NearSpecV3.lookupLast key entries = some e)
    (he' : NearSpecV3.lookupLast key' entries = some e')
    (hr : NearSpecV3.verifyReceiptProof r e = true)
    (hs : NearSpecV3.verifyReceiptProof s e' = true) : r = s := by
  subst key'
  have ee : e = e' := Option.some.inj (he.symm.trans he')
  subst e'
  exact source_roots_eq_of_same_proof e r s hr hs

end ZkFormal.NearV3
