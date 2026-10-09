import ZkFormal.NearV3.Rcpt.Candidates.DedupSourcePredecessor
import ZkFormal.NearV3.Rcpt.Link.SourceHash

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Any semantic block message independent of the repetition bit belongs to the
whole sequence. This includes all digest receives of computed blocks. -/
theorem chain_mem {tr : Trace Fp} {tt s : Nat} {bs : List SrcpB} {B : SrcpB}
    (hB : B∈bs) {m : Msg} {bb : Nat} {sd : Bool}
    (hm : ∀ rep, m∈DedupRender.blockMsgs B rep bb sd) : m∈chainMsgs tr tt s bs bb sd := by
  induction bs generalizing s with
  | nil => simp at hB
  | cons C bs ih =>
    simp only [chainMsgs, List.mem_append]
    rcases List.mem_cons.mp hB with rfl | hB
    · exact Or.inl (hm _)
    · exact Or.inr (ih hB)

theorem root_recv {tr : Trace Fp} {tt : Nat} {bs : List SrcpB} {B : SrcpB}
    (hB : B∈bs) (hd : B.dup=false) :
    digMsg (msgId K_SRC B.qe) B.le B.root∈sourceMsgs tr tt bs B_DIGEST false := by
  simp only [sourceMsgs, show B_DIGEST≠B_SIZE by decide, ite_false]
  apply chain_mem hB
  intro rep
  simp [DedupRender.blockMsgs, DedupRender.rootMsgs, hd, B_DIGEST, B_RCL, B_SRC]

theorem item_recv {tr : Trace Fp} {tt : Nat} {bs : List SrcpB} {B : SrcpB}
    (hB : B∈bs) (hd : B.dup=false) {it : SrcpItem} (hit : it∈B.path) :
    digMsg (msgId K_SRC it.pq) it.pl it.acc∈sourceMsgs tr tt bs B_DIGEST false := by
  simp only [sourceMsgs, show B_DIGEST≠B_SIZE by decide, ite_false]
  apply chain_mem hB
  intro rep
  apply List.mem_append.mpr
  right
  simp only [hd, Bool.false_eq_true, ite_false]
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨it, hit, by simp [srcpItemMsgs, B_DIGEST, B_BYTES]⟩

/-- Exact candidate traffic plus the closed SHA contract authenticates every
computed leaf/path chain. A skip requires a separate same-key public binding. -/
theorem source_hashes_of_sha {tr : Trace Fp} {tt : Nat} {bs : List SrcpB} (h : PayloadWf bs)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m, shaR B_BYTES m=cnt (payloadBytes bs++others) m)
    (hother : ∀ m∈others, ∀ a, m.head?=some a → a<P ∧ a%16≠K_SRC)
    (hdigest : ∀ m∈sourceMsgs tr tt bs B_DIGEST false, 0<shaS B_DIGEST m.toFp)
    {B : SrcpB} (hB : B∈bs) (hd : B.dup=false) : SourceHashes B (sourceDigest bs) := by
  have hw := h.computed hB hd
  have hpayload : ∀ p, p∈sourcePayloads B → p∈payloads B := by simp [payloads, hd]
  constructor
  · exact sourceDigest_eq h hB (p := (B.ql, B.leaf)) (hpayload _ (by simp [sourcePayloads]))
  · intro it hit
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hit
    obtain ⟨p, hp, hq, hl⟩ := source_predecessor hw i hi
    rw [he] at hq hl
    constructor
    · have hcanon : ∀ x∈it.acc, x<P := by
        intro x hx; exact hw.canon.2.2.2 it hit x (List.mem_append.mpr (Or.inr hx))
      have hh := source_sha_digest_bytes h hB (hpayload _ hp) hsha others hbytes hother hcanon
        (by rw [hq, hl]; exact hdigest _ (item_recv hB hd hit))
      simpa [hq] using hh
    · exact sourceDigest_eq h hB (p := (it.q, it.bytes)) (hpayload _
        (by simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map]
            exact Or.inr ⟨it, hit, rfl⟩))
  · obtain ⟨p, hp, hq, hl⟩ := source_final_payload hw
    have hcanon : ∀ x∈B.root, x<P := by
      intro x hx; exact hw.canon.2.2.1 x (List.mem_append.mpr (Or.inl hx))
    have hh := source_sha_digest_bytes h hB (hpayload _ hp) hsha others hbytes hother hcanon
      (by rw [hq, hl]; exact hdigest _ (root_recv hB hd))
    simpa [hq] using hh

/-- The actual spec Merkle recursion follows from a computed block's hash chain. -/
theorem computed_rootFromPath {B : SrcpB} (hw : BlockWf B) (dig : Nat → Bytes)
    (hh : SourceHashes B dig) :
    NearSpecV3.rootFromPath (sha256 (toBytes B.leaf)) (B.path.map SrcpItem.proofStep)=toBytes B.root := by
  rw [← hh.leaf]
  have hc : ∀ i (hi : i<B.path.length),
      toBytes B.path[i].acc=dig (B.ql+i) ∧
      dig (B.ql+i+1)=sha256 (toBytes B.path[i].bytes) := by
    intro i hi
    have hiw := hw.items i hi
    have hih := hh.items B.path[i] (List.getElem_mem hi)
    rw [hiw.2.1, hiw.1] at hih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih
  rw [srcp_path_chain B.path B.ql dig hc]
  have hqe : B.qe=B.ql+B.path.length := hw.root.1
  rw [← hqe, hh.root]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
