import ZkFormal.NearV3.Rcpt.Candidates.ParserConsumption

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

theorem pMany_le {α : Type} (p : NearSpecV3.P α) (hp : NonIncreasing p) (n : Nat) :
    NonIncreasing (pMany p n) := by
  induction n with
  | zero => intro bs a rest h; cases h; omega
  | succ n ih =>
    intro bs xs rest h
    unfold pMany at h
    obtain ⟨⟨a, tail⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨ys, tail'⟩, ht, h⟩ := bind_ok h
    cases h
    exact Nat.le_trans (ih _ _ _ ht) (hp _ _ _ ha)

theorem pVec_le {α : Type} (p : NearSpecV3.P α) (hp : NonIncreasing p) (w : String) :
    NonIncreasing (pVec w p) := by
  intro bs xs rest h
  unfold pVec at h
  obtain ⟨⟨n, tail⟩, hn, h⟩ := bind_ok h
  exact Nat.le_trans (pMany_le p hp n _ _ _ h) (pUInt_le 4 _ _ _ _ hn)

theorem pOption_le {α : Type} (p : NearSpecV3.P α) (hp : NonIncreasing p) (w : String) :
    NonIncreasing (pOption w p) := by
  intro bs v rest h
  unfold pOption at h
  obtain ⟨⟨t, tail⟩, ht, h⟩ := bind_ok h
  have htail := pUInt_le 1 _ _ _ _ ht
  dsimp only at h
  split at h
  · cases h; exact htail
  · obtain ⟨⟨x, last⟩, hx, h⟩ := bind_ok h
    cases h
    exact Nat.le_trans (hp _ _ _ hx) htail
  · cases h

theorem pAccountId_le (w : String) : NonIncreasing (pAccountId w) := by
  intro bs a rest h
  unfold pAccountId at h
  obtain ⟨⟨v, tail⟩, hv, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h; exact pBytes_le w _ _ _ hv
  · cases h

theorem pPublicKey_le (w : String) : NonIncreasing (pPublicKey w) := by
  intro bs a rest h
  unfold pPublicKey at h
  obtain ⟨⟨t, tail⟩, ht, h⟩ := bind_ok h
  dsimp only at h
  split at h
  all_goals try (cases h; done)
  all_goals
    obtain ⟨n, hn, h⟩ := bind_ok h
    obtain ⟨⟨v, last⟩, hv, h⟩ := bind_ok h
    cases h
    exact Nat.le_trans (pTake_le n w _ _ _ hv) (pUInt_le 1 _ _ _ _ ht)

theorem pSignature_le (w : String) : NonIncreasing (pSignature w) := by
  intro bs a rest h
  unfold pSignature at h
  obtain ⟨⟨t, tail⟩, ht, h⟩ := bind_ok h
  have htail := pUInt_le 1 _ _ _ _ ht
  dsimp only at h
  split at h
  · obtain ⟨⟨v, last⟩, hv, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · obtain ⟨_, he, _⟩ := bind_ok h; cases he
    · cases h
      exact Nat.le_trans (pTake_le 64 w _ _ _ hv) htail
  · obtain ⟨⟨v, last⟩, hv, h⟩ := bind_ok h
    cases h
    exact Nat.le_trans (pTake_le 65 w _ _ _ hv) htail
  · obtain ⟨⟨v, last⟩, hv, h⟩ := bind_ok h
    cases h
    exact Nat.le_trans (pTake_le 3309 w _ _ _ hv) htail
  · cases h

end ZkFormal.NearV3.Rcpt.Candidates
