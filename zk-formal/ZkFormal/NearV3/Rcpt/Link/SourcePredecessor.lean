import ZkFormal.NearV3.Rcpt.Link.SourceDigest

namespace ZkFormal.NearV3
open ZkFormal.Near

/-- Every Merkle accumulator lookup names the immediately preceding source payload. -/
theorem source_predecessor {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs)
    (i : Nat) (hi : i < B.path.length) :
    ∃ p ∈ sourcePayloads B, p.1 = B.path[i].pq ∧ p.2.length = B.path[i].pl := by
  have hf := h.items B hB i hi
  by_cases hz : i = 0
  · subst i
    refine ⟨(B.ql, B.leaf), by simp [sourcePayloads], ?_, ?_⟩
    · simpa using hf.2.1.symm
    · simpa [hf.2.2] using (h.len B hB).2.1
  · have hj : i - 1 < B.path.length := by omega
    let it := B.path[i - 1]
    have hm : it ∈ B.path := List.getElem_mem hj
    refine ⟨(it.q, it.bytes), ?_, ?_, ?_⟩
    · simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map]
      exact Or.inr ⟨it, hm, rfl⟩
    · have hp := (h.items B hB (i - 1) hj).1
      change B.path[i - 1].q = B.path[i].pq
      omega
    · have hs := ((h.len B hB).2.2 it hm).1
      have ha := ((h.len B hB).2.2 it hm).2
      rw [hf.2.2, if_neg hz]
      cases hd : it.dir <;> simp [SrcpItem.bytes, hd, hs, ha]

/-- A root digest lookup names the block's last source payload. -/
theorem source_final_payload {bs : List SrcpB} (h : SrcpWf bs) {B : SrcpB} (hB : B ∈ bs) :
    ∃ p ∈ sourcePayloads B, p.1 = B.qe ∧ p.2.length = B.le := by
  have hr := h.root B hB
  by_cases he : B.path = []
  · refine ⟨(B.ql, B.leaf), by simp [sourcePayloads], ?_, ?_⟩
    · simp [hr.1, SrcpB.lastQ, he]
    · simpa [hr.2, he] using (h.len B hB).2.1
  · have hn : 0 < B.path.length := by cases hh : B.path <;> simp_all
    have hi : B.path.length - 1 < B.path.length := by omega
    let it := B.path[B.path.length - 1]
    have hm : it ∈ B.path := List.getElem_mem hi
    refine ⟨(it.q, it.bytes), ?_, ?_, ?_⟩
    · simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map]
      exact Or.inr ⟨it, hm, rfl⟩
    · have hq := (h.items B hB (B.path.length - 1) hi).1
      change B.path[B.path.length - 1].q = B.qe
      simp only [SrcpB.lastQ] at hr
      omega
    · have hs := ((h.len B hB).2.2 it hm).1
      have ha := ((h.len B hB).2.2 it hm).2
      rw [hr.2, if_neg he]
      cases hd : it.dir <;> simp [SrcpItem.bytes, hd, hs, ha]

end ZkFormal.NearV3
