import ZkFormal.NearV3.Rcpt.Candidates.DedupSourceHashes

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

/-- A computed source block satisfies the actual receipt-proof verifier once
its RC digest and canonical SHA traffic have been linked. -/
theorem source_verifyReceiptProof_of_sha {tr : Trace Fp} {tt : Nat} {bs : List SrcpB}
    (h : PayloadWf bs) {shaS shaR : Nat → List Fp → Nat}
    (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m=cnt (sourceMsgs tr tt bs B_BYTES true++others) m)
    (hother : ∀ m∈others, ∀ a, m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs tr tt bs B_DIGEST false, 0<shaS B_DIGEST m.toFp)
    {B : SrcpB} (hB : B∈bs) (hd : B.dup=false) (e : NearSpecV3.ProofEntry)
    (hleaf : toBytes B.leaf=sha256 (u64 e.proof.toShard++encodeReceipts e.receipts))
    (hpath : e.proof.path=B.path.map SrcpItem.proofStep) :
    NearSpecV3.verifyReceiptProof (toBytes B.root) e=true := by
  have hh := source_hashes_of_sha h hsha others
    (by simpa only [source_bytes] using hbytes) hother hdigest hB hd
  unfold NearSpecV3.verifyReceiptProof
  dsimp only
  rw [hpath, ← hleaf, computed_rootFromPath (h.computed hB hd) (sourceDigest bs) hh]
  simp

/-- The SHA contract applies directly to a block chain extracted from arbitrary
candidate rows, with no old source-height or per-occurrence computation premise. -/
theorem BlockChain.verifyReceiptProof {tr : Trace Fp} {pub : List Fp} {tt stop : Nat}
    {bs : List SrcpB} (hL : TableLocal (DedupTable.table 24) tr tt pub)
    (hc : BlockChain tr tt 0 bs stop) {shaS shaR : Nat → List Fp → Nat}
    (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m=cnt (sourceMsgs tr tt bs B_BYTES true++others) m)
    (hother : ∀ m∈others, ∀ a, m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs tr tt bs B_DIGEST false, 0<shaS B_DIGEST m.toFp)
    {B : SrcpB} (hB : B∈bs) (hd : B.dup=false) (e : NearSpecV3.ProofEntry)
    (hleaf : toBytes B.leaf=sha256 (u64 e.proof.toShard++encodeReceipts e.receipts))
    (hpath : e.proof.path=B.path.map SrcpItem.proofStep) :
    NearSpecV3.verifyReceiptProof (toBytes B.root) e=true :=
  source_verifyReceiptProof_of_sha (hc.payload_wf hL) hsha others hbytes hother hdigest hB hd e hleaf hpath

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
