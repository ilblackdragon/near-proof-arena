import ZkFormal.NearV3.Rcpt.Candidates.ReceiptConsumption

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

theorem pValidatorStake_le : NonIncreasing pValidatorStake := by
  intro bs a rest h
  unfold pValidatorStake at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have ht := pTake_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu ht hh ha hp
    simp only [pU8, pU16, pU32, pU64, pU128, readU8, readU16, readU32, readU64, readU128] at *
    simp_all only [pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    grind only

theorem pCongestion_le : NonIncreasing pCongestion := by
  intro bs a rest h
  unfold pCongestion at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have ht := pTake_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu ht hh ha hp
    simp only [pU8, pU16, pU32, pU64, pU128, readU8, readU16, readU32, readU64, readU128] at *
    simp_all only [pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    grind only

theorem pBwRequest_le : NonIncreasing pBwRequest := by
  intro bs a rest h
  unfold pBwRequest at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have ht := pTake_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu ht hh ha hp
    simp only [pU8, pU16, pU32, pU64, pU128, readU8, readU16, readU32, readU64, readU128] at *
    simp_all only [pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    grind only

theorem pTrieSplit_le : NonIncreasing pTrieSplit := by
  intro bs a rest h
  unfold pTrieSplit at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have ht := pTake_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu ht hh ha hp
    simp only [pU8, pU16, pU32, pU64, pU128, readU8, readU16, readU32, readU64, readU128] at *
    simp_all only [pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    grind only

theorem pBwRequests_le : NonIncreasing pBwRequests := by
  intro bs a rest h
  unfold pBwRequests at h
  obtain ⟨⟨t, tail⟩, ht, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨u, hu, h⟩ := bind_ok h; cases hu
  · exact Nat.le_trans (pVec_le pBwRequest pBwRequest_le _ _ _ _ h) (pUInt_le 1 _ _ _ _ ht)

set_option maxHeartbeats 4000000 in
theorem pChunkInner_le : NonIncreasing pChunkInner := by
  intro bs a rest h
  unfold pChunkInner at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have ht := pTake_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu ht hh ha hp
    have hv := pVec_le pValidatorStake pValidatorStake_le
    have hc := pCongestion_le
    have hb := pBwRequests_le
    have ho := pOption_le pTrieSplit pTrieSplit_le
    unfold NonIncreasing at hv hc hb ho
    simp only [pU8, pU16, pU32, pU64, pU128, readU8, readU16, readU32, readU64, readU128] at *
    simp_all only [pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    grind only

theorem pChunkHeader_le : NonIncreasing pChunkHeader := by
  intro bs a rest h
  unfold pChunkHeader at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have ht := pTake_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu ht hh ha hp
    have hc := pChunkInner_le
    have hs := pSignature_le
    unfold NonIncreasing at hc hs
    simp only [pU8, pU16, pU32, pU64, pU128, readU8, readU16, readU32, readU64, readU128] at *
    simp_all only [pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    grind only

theorem pTransition_le : NonIncreasing pTransition := by
  intro bs a rest h
  unfold pTransition at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hu := pUInt_le
    have ht := pTake_le
    have hh := pHash_le
    have ha := pAccountId_le
    have hp := pPublicKey_le
    unfold NonIncreasing at hu ht hh ha hp
    have hv := pVec_le (pBytes "trie value") (pBytes_le _)
    unfold NonIncreasing at hv
    simp only [pU8, pU16, pU32, pU64, pU128, readU8, readU16, readU32, readU64, readU128] at *
    simp_all only [pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    grind only

end ZkFormal.NearV3.Rcpt.Candidates
