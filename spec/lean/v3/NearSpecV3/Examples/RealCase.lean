import NearSpecV3.Examples.RealCaseData

/-!
# Non-vacuity of `RelD0` on real nearcore cases (kernel-checked)

The Lean kernel evaluates the whole D0 relation (`decide +kernel`): claim and witness
decoding, block and chunk hashes, the backward walk, receipt-proof verification and
shuffle, the D0 `Runtime::apply` (multi-shard bandwidth scheduler, receipts, outcome
root), implicit transitions, the post-state root, the header comparison and the
Reed–Solomon encoded merkle root. Positive cases were accepted by nearcore's validator;
the negative ones are mutants nearcore rejects (a header field changed in claim and
witness; a duplicated receipt-proof key whose last value is corrupt), and the
`dup_key_last_good` mutant is one nearcore accepts (lenient `HashMap` decoding, last wins).
-/

namespace NearSpecV3.Examples

theorem relD0_00_h10014_s1 : RelD0 claim_00_h10014_s1 witness_00_h10014_s1 := by
  decide +kernel

theorem relD0_06_h10022_s0 : RelD0 claim_06_h10022_s0 witness_06_h10022_s0 := by
  decide +kernel

theorem relD0_00_h10014_s1_w_dup_key_last_good : RelD0 claim_00_h10014_s1_w_dup_key_last_good witness_00_h10014_s1_w_dup_key_last_good := by
  decide +kernel

theorem not_relD0_00_h10014_s1_hdr_prev_state_root : ¬ RelD0 claim_00_h10014_s1_hdr_prev_state_root witness_00_h10014_s1_hdr_prev_state_root := by
  decide +kernel

theorem not_relD0_00_h10014_s1_w_dup_key_last_bad : ¬ RelD0 claim_00_h10014_s1_w_dup_key_last_bad witness_00_h10014_s1_w_dup_key_last_bad := by
  decide +kernel

end NearSpecV3.Examples
