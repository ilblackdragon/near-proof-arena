import ZkFormal.NearV3.Rcpt.Candidates.DedupCounters
import ZkFormal.NearV3.Rcpt.Candidates.PartitionCapacity
import ZkFormal.NearV3.Rcpt.Render.Srcp.FromProofFacts
import ZkFormal.NearV3.Rcpt.Link.SourcePayload

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 ZkFormal.Near Render.SrcpGen

/-- Payload widths follow from the real selected proof decoder, without using the
old SrcpWf row cap. -/
theorem block_payload_widths {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (sources : List SrcList) {j : Nat}
    (hl : lookupLast (sources.getD j ⟨[],0,[]⟩).key w.entries = some (entryAt sources w.entries j)) :
    (block sources w.entries j).leaf.length = 32 ∧
      ∀ it ∈ (block sources w.entries j).path, it.bytes.length = 64 := by
  have hs := lookupLast_path_shape hw hl
  constructor
  · simp [block, blockOfProof, ArenaCore.sha256_length]
  · intro it hi
    have hh := proofItems_lengths (entryAt sources w.entries j).proof.path
      (nextQ sources w.entries j) 32 _ (ArenaCore.sha256_length _)
      (fun step hm => (hs step hm).1) it hi
    cases hd : it.dir <;> simp [SrcpItem.bytes, hd, hh.1, hh.2]

def payloadWeights (bs : List SrcpB) : List Nat :=
  bs.flatMap fun B => (sourcePayloads B).map fun p => msgRows p.2.length

def sourceWeights (sources : List SrcList) (entries : List ProofEntry) : List Nat :=
  payloadWeights ((blocks sources entries).filter fun B => !B.dup)

private theorem one_weight_sum (B : SrcpB) (hl : B.leaf.length = 32)
    (hp : ∀ it ∈ B.path, it.bytes.length = 64) :
    ((sourcePayloads B).map fun p => msgRows p.2.length).sum = 18 + 35 * B.path.length := by
  have he : (B.path.map fun it => msgRows it.bytes.length) = B.path.map (fun _ => 35) := by
    apply List.map_congr_left
    intro it hi
    rw [hp it hi]
    rfl
  simp only [sourcePayloads, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, hl, List.map_map, Function.comp_def]
  rw [he, List.map_const', List.sum_replicate_nat]
  simp only [msgRows]
  omega

private theorem payloadWeights_sum (bs : List SrcpB)
    (hw : ∀ B ∈ bs, B.leaf.length = 32 ∧ ∀ it ∈ B.path, it.bytes.length = 64) :
    (payloadWeights bs).sum = 18 * bs.length + 35 * (bs.map fun B => B.path.length).sum := by
  induction bs with
  | nil => simp [payloadWeights]
  | cons B rest ih =>
    have hb := hw B (by simp)
    have ht := ih (fun C hC => hw C (by simp [hC]))
    simp only [payloadWeights, List.flatMap_cons, List.sum_append] at *
    rw [one_weight_sum B hb.1 hb.2, ht]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem payloadWeights_max (bs : List SrcpB)
    (hw : ∀ B ∈ bs, B.leaf.length = 32 ∧ ∀ it ∈ B.path, it.bytes.length = 64) :
    ∀ a ∈ payloadWeights bs, a ≤ 35 := by
  intro a ha
  obtain ⟨B, hB, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have hb := hw B hB
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hi, rfl⟩
  · simp [hb.1, msgRows]
  · simp [hb.2 it hi, msgRows]

theorem sourceWeights_exact {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (sources : List SrcList)
    (hs : ∀ j, j < sources.length → ∃ e,
      lookupLast (sources.getD j ⟨[],0,[]⟩).key w.entries = some e) :
    (sourceWeights sources w.entries).sum =
      sourceShaFor (computedLists sources w.entries) (computedPaths sources w.entries) ∧
      ∀ a ∈ sourceWeights sources w.entries, a ≤ 35 := by
  have hb : ∀ B ∈ (blocks sources w.entries).filter (fun B => !B.dup),
      B.leaf.length = 32 ∧ ∀ it ∈ B.path, it.bytes.length = 64 := by
    intro B hB
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hB).1
    exact block_payload_widths hw sources (entryAt_lookup sources w.entries (hs j (List.mem_range.mp hj)))
  refine ⟨?_, payloadWeights_max _ hb⟩
  have he := payloadWeights_sum _ hb
  simpa only [sourceWeights, sourceShaFor, msgRows, computedLists, computedPaths,
    Nat.mul_comm] using he

/-- Actual decoded source preimages, rather than an abstract weight envelope, admit
two whole-message log23 SHA partitions. The SHA AIR/bus implementation is still separate. -/
theorem relD0a_sha_partition {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    (splitBudget (2 ^ 23) (sourceWeights p.lists w.entries)).1.sum ≤ 2 ^ 23 ∧
      (splitBudget (2 ^ 23) (sourceWeights p.lists w.entries)).2.sum ≤ 2 ^ 23 := by
  obtain ⟨_, _, hs⟩ := relD0a_inputs h hp hf hw
  obtain ⟨he, hm⟩ := sourceWeights_exact hw p.lists hs
  apply source_sha_partition_capacity _ hm
  rw [he]
  exact (relD0a_work_bounds h hp hf hw).2.1

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
