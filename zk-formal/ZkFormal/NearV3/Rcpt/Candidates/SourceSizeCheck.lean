import ZkFormal.NearV3.Rcpt.Candidates.SourceSize

namespace ZkFormal.NearV3.Rcpt.Candidates

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation of the candidate shape model only; active AIR and security pins are unchanged. -/
theorem partitionSize_g2 : partitionSize 2 = 8190337 := by decide +kernel

theorem partitionSize_g2_margin : partitionSize 2 + 198271 = 8388608 := by
  rw [partitionSize_g2]

end ZkFormal.NearV3.Rcpt.Candidates
