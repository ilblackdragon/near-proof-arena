import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra

/-- The unchanged raw witness cap leaves genuine padding in the right partition;
no path-depth premise or new source-count restriction is introduced. -/
theorem relD0a_partition_padding {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w) :
    DedupRender.R (blocks p.lists w.entries) ≤ 2 * 2 ^ 23 - 2 := by
  have hh := relD0a_row_bound h hp hf hw
  omega

/-- Actual accepted input renders into two physical log23 source tables with
all local constraints and multiplicity-bit checks. This theorem does not assert
admission by the frozen maxLog22 protocol family. -/
theorem relD0a_partition_local {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hw : decodeStateWitness raw = .ok w)
    {tr : Trace Fp} {left right carryBus : Nat} {pub : List Fp}
    (hl : tr.log left = 23) (hr : tr.log right = 23)
    (hcl : ∀ r, r < tr.height left → ∀ x,
      tr.cell left r x = Fp.ofNat (DedupRender.cell (blocks p.lists w.entries)
        (sourceRepeated p.lists) r x))
    (hcr : ∀ r, r < tr.height right → ∀ x,
      tr.cell right r x = Fp.ofNat (DedupRender.cell (blocks p.lists w.entries)
        (sourceRepeated p.lists) (tr.height right - 1 + r) x)) :
    TableLocal (DedupPartitionTable.leftTable carryBus) tr left pub ∧
    TableLocal (DedupPartitionTable.rightTable carryBus) tr right pub := by
  have hfacts := relD0a_table_facts h hp hf hw
  have hpad := relD0a_partition_padding h hp hf hw
  constructor
  · apply DedupPartitionTable.left_local hfacts _ _ _ _ hcl
    · omega
    · omega
    · simp [Trace.height, hl]
    · simpa [Trace.height, hl] using hpad
  · apply DedupPartitionTable.right_local hfacts _ _ _ _ hcr
    · omega
    · omega
    · simp [Trace.height, hr]
    · simpa [Trace.height, hr] using hpad

end ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
