import ZkFormal.NearV3.Candidates.CurrentFamilyChecks
namespace ZkFormal.NearV3.Candidates.CurrentFamily
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
/-- Exact current static bound; exceeds the unchanged8MiB cap. -/
theorem bytes_two : bytes 2=9498374 := by
  unfold bytes
  rw [shapes_two]
  decide +kernel
theorem exceeds_cap : 8388608 < bytes 2 := by rw [bytes_two]; decide
end ZkFormal.NearV3.Candidates.CurrentFamily
