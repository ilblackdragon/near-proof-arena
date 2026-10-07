import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofInputFacts
import ZkFormal.NearV3.Rcpt.Render.Srcp.CounterFacts

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open Render.SrcpGen

/-- Counter facts used by local source constraints, with no height or depth premise. -/
structure BlockFacts (B : SrcpB) : Prop where
  counter : CounterFacts B
  pq : ∀ i (hi : i < B.path.length), B.path[i].pq = B.ql + i

theorem BlockFacts.item (B : SrcpB) (h : BlockFacts B) (i : Nat) (hi : i < B.path.length) :
    (B.path.getD i default).q = B.ql + 1 + i ∧
    (B.path.getD i default).pq = B.ql + i ∧
    (B.path.getD i default).pl = if i = 0 then 32 else 64 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact ⟨h.counter.item_q i hi, h.pq i hi, h.counter.item_pl i hi⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 Render.SrcpGen

/-- Every executable compiled block supplies all local counter premises. -/
theorem block_facts (sources : List SrcList) (entries : List ProofEntry) (j : Nat) :
    DedupRender.BlockFacts (block sources entries j) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [block, blockOfProof, nextQ]
    omega
  · intro i hi
    exact (blockOfProof_items _ _ _ _ _ i hi).1
  · intro i hi
    exact (blockOfProof_items _ _ _ _ _ i hi).2.2
  · exact (blockOfProof_root _ _ _ _ _).1
  · exact (blockOfProof_root _ _ _ _ _).2
  · intro i hi
    exact (blockOfProof_items _ _ _ _ _ i hi).2.1

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
