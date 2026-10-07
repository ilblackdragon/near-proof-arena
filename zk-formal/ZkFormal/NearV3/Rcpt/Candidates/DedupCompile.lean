import ZkFormal.NearV3.Rcpt.Candidates.FirstSources
import ZkFormal.NearV3.Rcpt.Candidates.DedupRender
import ZkFormal.NearV3.Rcpt.Candidates.PreparedMetadata
import ZkFormal.NearV3.Rcpt.Render.Srcp.FromProof

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 ZkFormal.Near Render.SrcpGen

/-- Missing entries have a deterministic fallback; successful actual validation proves
that this fallback is never selected at any prepared source occurrence. -/
def entryAt (sources : List SrcList) (entries : List ProofEntry) (j : Nat) : ProofEntry :=
  (lookupLast (sources.getD j ⟨[],0,[]⟩).key entries).getD ⟨[], [], ⟨0,0,[]⟩⟩

def messageWeight (sources : List SrcList) (entries : List ProofEntry) (j : Nat) : Nat :=
  if Public.sourceDup sources j then 0 else 1 + (entryAt sources entries j).proof.path.length

def nextQ (sources : List SrcList) (entries : List ProofEntry) (j : Nat) : Nat :=
  1 + ((List.range j).map (messageWeight sources entries)).sum

def block (sources : List SrcList) (entries : List ProofEntry) (j : Nat) : SrcpB :=
  blockOfProof (sources.getD j ⟨[],0,[]⟩).root (Public.sourceDup sources j)
    j (nextQ sources entries j) (entryAt sources entries j)

/-- Honest candidate input uses every public occurrence in order; duplicate blocks
retain semantic data but their renderer emits only the header. -/
def blocks (sources : List SrcList) (entries : List ProofEntry) : List SrcpB :=
  (List.range sources.length).map (block sources entries)

theorem blocks_length (sources : List SrcList) (entries : List ProofEntry) :
    (blocks sources entries).length = sources.length := by simp [blocks]

theorem selected_paths (sources : List SrcList) (entries : List ProofEntry) :
    (((blocks sources entries).filter fun B => !B.dup).map fun B => B.path.length).sum =
      pathCount (firstSourceEntries sources (entryAt sources entries)) := by
  simp only [blocks, List.filter_map, List.map_map, Function.comp_def, block, blockOfProof, proofItems_length,
    firstSourceEntries, firstSourceIndices, pathCount]

theorem entryAt_lookup (sources : List SrcList) (entries : List ProofEntry) {j : Nat}
    (h : ∃ e, lookupLast (sources.getD j ⟨[],0,[]⟩).key entries = some e) :
    lookupLast (sources.getD j ⟨[],0,[]⟩).key entries = some (entryAt sources entries j) := by
  obtain ⟨e, he⟩ := h
  unfold entryAt
  rw [he]
  rfl

/-- Source row capacity now follows from actual raw witness size and prepared source
selection, with no repeated-path depth premise. -/
theorem raw_row_bound {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (hb : lenT raw ≤ witnessBytes)
    (sources : List SrcList) (hc : sources.length ≤ sourceLists)
    (hs : ∀ j, j < sources.length → ∃ e,
      lookupLast (sources.getD j ⟨[],0,[]⟩).key w.entries = some e) :
    DedupRender.R (blocks sources w.entries) ≤ 16334272 := by
  apply DedupRender.R_bound
  · simpa only [blocks_length] using hc
  · rw [selected_paths]
    exact firstSourceEntries_raw_budget hw hb sources (entryAt sources w.entries)
      (fun j hj => entryAt_lookup sources w.entries (hs j hj))

/-- The actual successful D0a/preparation paths imply the honest dedup renderer's
row bound. This is a capacity result, not yet an AIR completeness theorem. -/
theorem relD0a_inputs {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    lenT raw ≤ witnessBytes ∧ p.lists.length ≤ sourceLists ∧
      (∀ j, j < p.lists.length → ∃ e,
        lookupLast (p.lists.getD j ⟨[],0,[]⟩).key w.entries = some e) := by
  obtain ⟨raw', codes', w', hf', _, hb, _⟩ := relD0a_source_paths h
  have he := Except.ok.inj (hf.symm.trans hf')
  have heraw := (Prod.mk.inj he).1
  subst raw'
  obtain ⟨k, sw, hk, hsw, hv, _⟩ := relD0a_sources_verified h
  have hd : decodeW wb = .ok w := by simp [decodeW, hf, hw, bind, Except.bind]
  have hew := Except.ok.inj (hsw.symm.trans hd)
  subst sw
  have ha := preparedSourceLists_authenticated w.entries k.H.shardId k.sourceBlks hv
    (Assembly.prepD0_source_lists hp hk)
  refine ⟨hb, prepD0_source_count hp, ?_⟩
  intro j hj
  have hm : p.lists.getD j ⟨[],0,[]⟩ ∈ p.lists := by
    rw [← List.getElem_eq_getD (h := hj) ⟨[],0,[]⟩]
    exact List.getElem_mem hj
  obtain ⟨e, he, _, _, _⟩ := ha _ hm
  exact ⟨e, he⟩

/-- The executable candidate renderer fits the global deduplicated source envelope. -/
theorem relD0a_row_bound {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    DedupRender.R (blocks p.lists w.entries) ≤ 16334272 := by
  obtain ⟨hb, hc, hs⟩ := relD0a_inputs h hp hf hw
  exact raw_row_bound hw hb p.lists hc hs

def computedLists (sources : List SrcList) (entries : List ProofEntry) : Nat :=
  ((blocks sources entries).filter fun B => !B.dup).length

def computedPaths (sources : List SrcList) (entries : List ProofEntry) : Nat :=
  (((blocks sources entries).filter fun B => !B.dup).map fun B => B.path.length).sum

theorem raw_work_bounds {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (hb : lenT raw ≤ witnessBytes)
    (sources : List SrcList) (hc : sources.length ≤ sourceLists)
    (hs : ∀ j, j < sources.length → ∃ e,
      lookupLast (sources.getD j ⟨[],0,[]⟩).key w.entries = some e) :
    sourcePreimagesFor (computedLists sources w.entries) (computedPaths sources w.entries) ≤ 16332288 ∧
    sourceShaFor (computedLists sources w.entries) (computedPaths sources w.entries) ≤ 8932712 ∧
    computedLists sources w.entries + computedPaths sources w.entries ≤ 256184 := by
  have hl : computedLists sources w.entries ≤ sourceLists := by
    have hh := List.length_filter_le (fun B : SrcpB => !B.dup) (blocks sources w.entries)
    rw [blocks_length] at hh
    exact Nat.le_trans hh hc
  have hp : computedPaths sources w.entries ≤ distinctPathItems := by
    rw [computedPaths, selected_paths]
    exact firstSourceEntries_raw_budget hw hb sources (entryAt sources w.entries)
      (fun j hj => entryAt_lookup sources w.entries (hs j hj))
  have hu := unique_bounds _ _ hl hp
  refine ⟨hu.2.1, hu.2.2, ?_⟩
  simp only [sourceLists, distinctPathItems, witnessBytes] at hl hp
  omega

/-- The actual honest source compiler obeys source-preimage, SHA-row, and message-count
bounds. Partition placement and SHA AIR rendering are separate obligations. -/
theorem relD0a_work_bounds {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    sourcePreimagesFor (computedLists p.lists w.entries) (computedPaths p.lists w.entries) ≤ 16332288 ∧
    sourceShaFor (computedLists p.lists w.entries) (computedPaths p.lists w.entries) ≤ 8932712 ∧
    computedLists p.lists w.entries + computedPaths p.lists w.entries ≤ 256184 := by
  obtain ⟨hb, hc, hs⟩ := relD0a_inputs h hp hf hw
  exact raw_work_bounds hw hb p.lists hc hs

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
