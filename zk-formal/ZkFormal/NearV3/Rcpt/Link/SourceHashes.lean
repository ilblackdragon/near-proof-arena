import ZkFormal.NearV3.Rcpt.Link.SourcePredecessor
import ZkFormal.NearV3.Rcpt.Link.SourceHash

namespace ZkFormal.NearV3
open ZkFormal.Near ZkFormal.Algebra NearSpec

private theorem root_recv {bs : List SrcpB} {B : SrcpB} (hB : B ∈ bs) :
    digMsg (msgId K_SRC B.qe) B.le B.root ∈ (srcpTraffic bs).recvs B_DIGEST := by
  simp only [srcpTraffic, show B_DIGEST ≠ B_SIZE by decide, ite_false, List.mem_flatMap]
  refine ⟨B, hB, ?_⟩
  simp [srcpBlockMsgs, srcpRootMsgs, B_DIGEST, B_BYTES, B_SRC, B_RCL]

private theorem item_recv {bs : List SrcpB} {B : SrcpB} (hB : B ∈ bs)
    {it : SrcpItem} (hit : it ∈ B.path) :
    digMsg (msgId K_SRC it.pq) it.pl it.acc ∈ (srcpTraffic bs).recvs B_DIGEST := by
  simp only [srcpTraffic, show B_DIGEST ≠ B_SIZE by decide, ite_false, List.mem_flatMap]
  refine ⟨B, hB, ?_⟩
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨it, hit, by simp [srcpItemMsgs]⟩

/-- Exact source BYTES and DIGEST linking supplies the full Merkle hash-chain contract.
The SHA contract is closed elsewhere; all source-index isolation and lookup lengths are
proved here from the existing source-table view. -/
theorem source_hashes_of_sha {bs : List SrcpB} (h : SrcpWf bs)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m = cnt ((srcpTraffic bs).sends B_BYTES ++ others) m)
    (hother : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_SRC)
    (hdigest : ∀ m ∈ (srcpTraffic bs).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    {B : SrcpB} (hB : B ∈ bs) : SourceHashes B (sourceDigest bs) := by
  constructor
  · exact sourceDigest_eq h hB (p := (B.ql, B.leaf)) (by simp [sourcePayloads])
  · intro it hit
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hit
    obtain ⟨p, hp, hq, hl⟩ := source_predecessor h hB i hi
    rw [he] at hq hl
    constructor
    · have hd : ∀ x ∈ it.acc, x < P := by
        intro x hx; exact (h.canon B hB).2.2.2 it hit x (List.mem_append.mpr (Or.inr hx))
      have hh := source_sha_digest_bytes h hB hp hsha others hbytes hother hd
        (by rw [hq, hl]; exact hdigest _ (item_recv hB hit))
      simpa [hq] using hh
    · exact sourceDigest_eq h hB (p := (it.q, it.bytes))
        (by simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map]
            exact Or.inr ⟨it, hit, rfl⟩)
  · obtain ⟨p, hp, hq, hl⟩ := source_final_payload h hB
    have hd : ∀ x ∈ B.root, x < P := by
      intro x hx; exact (h.canon B hB).2.2.1 x (List.mem_append.mpr (Or.inl hx))
    have hh := source_sha_digest_bytes h hB hp hsha others hbytes hother hd
      (by rw [hq, hl]; exact hdigest _ (root_recv hB))
    simpa [hq] using hh

end ZkFormal.NearV3
