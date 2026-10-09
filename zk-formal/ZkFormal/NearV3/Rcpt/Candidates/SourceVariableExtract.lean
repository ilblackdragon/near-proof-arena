import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableSound
import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22BoundarySound

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

/-- Physical local validity and actual carry balance recover one semantic source
sequence. Heights may differ, and no honest placement or boundary equality is
supplied. Whole-AIR isolation must still supply the displayed carry counts. -/
theorem balanced_source_blocks {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hbal : ∀ bus∈([64,65,66] : List Nat), ∀ m,
      boundaryCount tr a b c d pub bus true m=boundaryCount tr a b c d pub bus false m) :
    ∃ bs stop,
      TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub ∧
      DedupProof.BlockChain (variableTrace tr a b c d) 0 0 bs stop ∧
      bs≠[] ∧ DedupRender.R bs≤2^24 := by
  obtain ⟨hab,hbc,hcd⟩ := boundaries_cells hbal
  exact variable_blocks ha hb hc hd hab hbc hcd

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
