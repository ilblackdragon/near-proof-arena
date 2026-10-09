import ZkFormal.NearV3.Rcpt.Candidates.ParserComposite

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

/-- The actual receipt parser cannot manufacture additional unconsumed witness bytes. -/
theorem pReceipt_le : NonIncreasing NearSpecV3.pReceipt := by
  intro bs a rest h
  unfold NearSpecV3.pReceipt at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu hh ha hp
    simp only [pU8, pU32, pU64, pU128, readU8, readU32, readU64, readU128] at *
    grind only

end ZkFormal.NearV3.Rcpt.Candidates
