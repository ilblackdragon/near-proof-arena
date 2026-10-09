import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficProof
import ZkFormal.NearV3.Rcpt.Candidates.PreparedNonempty
import ZkFormal.NearV3.Rcpt.Candidates.DedupSha

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.SrcpGen

/-- Every actual compiled source block has the widths required by its bus contract. -/
theorem relD0a_block_widths {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    ∀ B ∈ blocks p.lists w.entries, B.root.length = 32 ∧ B.leaf.length = 32 ∧
      ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32 := by
  obtain ⟨_, _, hs⟩ := relD0a_inputs h hp hf hw
  intro B hB
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hB
  have hj' := List.mem_range.mp hj
  have hm : p.lists.getD j ⟨[],0,[]⟩ ∈ p.lists := by
    rw [← List.getElem_eq_getD (h := hj') ⟨[],0,[]⟩]
    exact List.getElem_mem hj'
  have hroot := Assembly.prepD0_source_roots hp _ hm
  have hlookup := entryAt_lookup p.lists w.entries (hs j hj')
  have hpath := lookupLast_path_shape hw hlookup
  refine ⟨?_, ?_, ?_⟩
  · simpa [block, blockOfProof] using hroot
  · simp [block, blockOfProof, ArenaCore.sha256_length]
  · exact proofItems_lengths _ _ _ _ (ArenaCore.sha256_length _)
      (fun step hstep => (hpath step hstep).1)

/-- Nonempty candidate blocks follow from the actual successful native walk and prep. -/
theorem relD0a_blocks_nonempty {budget : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p) (entries : List ProofEntry) :
    blocks p.lists entries ≠ [] := by
  obtain ⟨k, _, hk, _, _, _⟩ := relD0a_sources_verified h
  have hn := prepD0_sources_nonempty hp hk
  intro hz
  have he := congrArg List.length hz
  rw [blocks_length, List.length_nil] at he
  exact hn (List.length_eq_zero_iff.mp he)

/-- On real valid inputs, the concrete logical source renderer realizes all five bus
contracts. Capacity/partition placement and local AIR legality are separate obligations. -/
theorem relD0a_table_traffic {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w)
    {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hH : DedupRender.R (blocks p.lists w.entries) ≤ tr.height tt)
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat
      (DedupRender.cell (blocks p.lists w.entries) (sourceRepeated p.lists) r x)) :
    TableTraffic DedupTable.interactions tr tt pub
      (DedupRender.traffic (blocks p.lists w.entries) (sourceRepeated p.lists)) := by
  exact DedupRender.table_traffic (relD0a_blocks_nonempty h hp w.entries)
    (sourceRepeated p.lists) (relD0a_block_widths h hp hf hw) hH hc

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
