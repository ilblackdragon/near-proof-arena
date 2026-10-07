import ZkFormal.NearV3.Rcpt.Candidates.DedupBlockFacts
import ZkFormal.NearV3.Rcpt.Candidates.DedupActualTraffic
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRepeated
import ZkFormal.NearV3.Rcpt.Candidates.DedupCounters

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender

/-- Semantic data used by the candidate's local completeness proof. No AIR
satisfaction, row-cap, path-depth, or field-canonicality premise is hidden here. -/
structure TableFacts (bs : List SrcpB) (repeated : Nat → Bool) : Prop where
  nonempty : bs ≠ []
  block : ∀ B ∈ bs, BlockFacts B
  index : ∀ i, i < bs.length → (bs.getD i default).j = i
  first_q : (bs.getD 0 default).ql = 1
  first_dup : (bs.getD 0 default).dup = false
  next_q : ∀ i, i + 1 < bs.length →
    (bs.getD (i + 1) default).ql =
      if (bs.getD i default).dup then (bs.getD i default).ql
      else (bs.getD i default).lastQ + 1
  dup_rep : ∀ i, i < bs.length → (bs.getD i default).dup = true → repeated i = true
  rep_length : ∀ i, i < bs.length → repeated i = true → (bs.getD i default).L = 12

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 Render.SrcpGen

theorem blocks_getD (sources : List SrcList) (entries : List ProofEntry) (j : Nat)
    (hj : j < sources.length) :
    (blocks sources entries).getD j default = block sources entries j := by
  have hb : j < (blocks sources entries).length := by simpa [blocks_length] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  simp [blocks]

/-- Actual accepted native input supplies every semantic local-completeness field. -/
theorem relD0a_table_facts {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    DedupRender.TableFacts (blocks p.lists w.entries) (sourceRepeated p.lists) := by
  have hn := relD0a_blocks_nonempty h hp w.entries
  have hsrc : 0 < p.lists.length := by
    have hb : 0 < (blocks p.lists w.entries).length := by cases he : blocks p.lists w.entries <;> simp_all
    simpa [blocks_length] using hb
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
    exact block_facts p.lists w.entries i
  · intro i hi
    rw [blocks_length] at hi
    rw [blocks_getD _ _ _ hi]
    rfl
  · rw [blocks_getD _ _ _ hsrc]
    simp [block, blockOfProof, nextQ]
  · rw [blocks_getD _ _ _ hsrc]
    simp [block, blockOfProof, Public.sourceDup]
  · intro i hi
    rw [blocks_length] at hi
    rw [blocks_getD _ _ _ hi, blocks_getD _ _ _ (by omega)]
    have hh := nextQ_succ p.lists w.entries i
    simp only [block, blockOfProof, SrcpB.lastQ, proofItems_length]
    simp only [messageWeight] at hh
    split <;> simp_all <;> omega
  · intro i hi hd
    rw [blocks_length] at hi
    rw [blocks_getD _ _ _ hi] at hd
    exact sourceDup_repeated p.lists hi hd
  · intro i hi hr
    rw [blocks_length] at hi
    rw [blocks_getD _ _ _ hi]
    exact relD0a_repeated_L12 h hp hf hw hi hr

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
