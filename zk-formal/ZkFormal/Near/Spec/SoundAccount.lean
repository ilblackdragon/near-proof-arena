import ZkFormal.Near.Spec.SoundWalk

/-!
# ZkFormal.Near.Spec.SoundAccount — `Account.encode`/`decode` round trips
-/

namespace ZkFormal.Near

open NearSpec

namespace Sound

theorem leN_leNat (l : Bytes) : leN l.length (leNat l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.length_cons, leN, leNat]
    have h1 : (b.toNat + 256 * leNat l) % 256 = b.toNat := by have := b.toNat_lt; omega
    have h2 : (b.toNat + 256 * leNat l) / 256 = leNat l := by have := b.toNat_lt; omega
    rw [h1, h2, ih]; simp

theorem leNat_lt (l : Bytes) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b l ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := b.toNat_lt; omega

theorem account_encode_length (a : Account) (h : a.codeHash.length = 32) :
    (Account.encode a).length = 72 := by
  simp [Account.encode, u128, u64, leN_length, h]

/-- Decoded accounts have in-range fields. -/
theorem decode_wf {b : Bytes} {a : Account} (h : Account.decode b = some a) :
    a.amount < Params.u128Max ∧ a.locked < Params.two128 ∧ a.codeHash.length = 32 ∧
      a.storageUsage < Params.two64 ∧ b.length = 72 := by
  unfold Account.decode at h
  split at h
  · rename_i hl
    dsimp only at h
    split at h
    · simp at h
    · rename_i hne
      simp only [Option.some.injEq] at h; subst h
      have h1 := leNat_lt (b.take 16)
      have h2 := leNat_lt ((b.drop 16).take 16)
      have h3 := leNat_lt (b.drop 64)
      simp [hl] at h1 h2 h3
      refine ⟨?_, ?_, ?_, ?_, hl⟩
      · show leNat (List.take 16 b) < _
        simp [Params.u128Max] at hne ⊢; omega
      · simpa [Params.two128] using h2
      · simp [hl]
      · simpa [Params.two64] using h3
  · simp at h

/-- `encode ∘ decode = id` on decodable bytes. -/
theorem encode_decode {b : Bytes} {a : Account} (h : Account.decode b = some a) :
    Account.encode a = b := by
  have hl := (decode_wf h).2.2.2.2
  unfold Account.decode at h
  simp only [hl, ↓reduceIte] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h
    simp only [Account.encode, u128, u64]
    have e1 := leN_leNat (b.take 16)
    have e2 := leN_leNat ((b.drop 16).take 16)
    have e3 := leN_leNat (b.drop 64)
    simp [hl] at e1 e2 e3
    rw [e1, e2, e3]
    have d64 : b.drop 64 = (b.drop 32).drop 32 := by simp [List.drop_drop]
    have d32 : b.drop 32 = (b.drop 16).drop 16 := by simp [List.drop_drop]
    simp only [List.append_assoc]
    rw [d64, List.take_append_drop, d32, List.take_append_drop, List.take_append_drop]

/-- `decode ∘ encode = some` on in-range accounts. -/
theorem decode_encode (a : Account) (h1 : a.amount < Params.u128Max)
    (h2 : a.locked < Params.two128) (h3 : a.codeHash.length = 32)
    (h4 : a.storageUsage < Params.two64) : Account.decode (Account.encode a) = some a := by
  have hl := account_encode_length a h3
  unfold Account.decode
  simp only [hl, ↓reduceIte]
  have l1 : (u128 a.amount).length = 16 := leN_length 16 _
  have l2 : (u128 a.locked).length = 16 := leN_length 16 _
  have t1 : (Account.encode a).take 16 = u128 a.amount := by
    simp [Account.encode, l1]
  have t2 : ((Account.encode a).drop 16).take 16 = u128 a.locked := by
    simp [Account.encode, l1, l2]
  have e : Account.encode a = (u128 a.amount ++ u128 a.locked) ++ (a.codeHash ++ u64 a.storageUsage) := by
    simp [Account.encode]
  have t3 : ((Account.encode a).drop 32).take 32 = a.codeHash := by
    rw [e, List.drop_left' (by simp [l1, l2])]
    exact List.take_left' h3
  have t4 : (Account.encode a).drop 64 = u64 a.storageUsage := by
    rw [e, List.append_assoc, ← List.append_assoc (u128 a.locked), ← List.append_assoc]
    exact List.drop_left' (by simp [l1, l2, h3])
  have hm : Params.u128Max < 256 ^ 16 := by decide
  rw [t1, t2, t3, t4, u128, u128, u64,
    NearSpec.leNat_leN 16 _ (by omega),
    NearSpec.leNat_leN 16 _ (by simpa [Params.two128] using h2),
    NearSpec.leNat_leN 8 _ (by simpa [Params.two64] using h4)]
  simp [Nat.ne_of_lt h1]

end Sound

end ZkFormal.Near
