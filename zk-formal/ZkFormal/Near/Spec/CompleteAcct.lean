import ZkFormal.Near.Spec.Prune

/-!
# ZkFormal.Near.Spec.CompleteAcct — account codec and flat-run helper lemmas

* `decode_some` / `decode_encode` — AccountV1 decoding: widths of a decoded
  account, and decoding of an encoded account with fields in range;
* `amtAt_*` — the flat amount of a slot before receipt `r`;
* `nibbles_lt`, `accountKeyPath_length` — account keys are nibble paths of
  at most 130 nibbles for valid account ids.
-/

namespace ZkFormal.Near.Prune

open NearSpec NearSpec.TransferV1

theorem leNat_lt : ∀ (l : Bytes), leNat l < 256 ^ l.length
  | [] => by simp [leNat]
  | b :: l => by
    have := leNat_lt l
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have : 256 * leNat l ≤ 256 * (256 ^ l.length - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 256 * (256 ^ l.length - 1) = 256 ^ l.length * 256 - 256 := by
      rw [Nat.mul_sub, Nat.mul_comm]
    omega

theorem two128_eq : Params.two128 = 256 ^ 16 := by decide
theorem u128Max_eq : Params.u128Max + 1 = Params.two128 := by decide
theorem two64_eq : Params.two64 = 256 ^ 8 := by decide

/-- Widths of a decoded account. -/
theorem decode_some {b : Bytes} {a : Account} (h : Account.decode b = some a) :
    b.length = 72 ∧ a.amount < Params.u128Max ∧ a.locked < Params.two128 ∧
      a.codeHash.length = 32 ∧ a.storageUsage < Params.two64 := by
  unfold Account.decode at h
  split at h
  · rename_i hl
    dsimp only at h
    split at h
    · cases h
    · rename_i hne
      simp only [Option.some.injEq] at h; subst h
      have h1 := leNat_lt (b.take 16)
      have h2 := leNat_lt ((b.drop 16).take 16)
      have h4 := leNat_lt (b.drop 64)
      simp only [List.length_take, List.length_drop, hl] at h1 h2 h4
      refine ⟨hl, ?_, ?_, ?_, ?_⟩
      · have := u128Max_eq; rw [two128_eq] at this
        simp only at hne ⊢
        have : leNat (List.take 16 b) < 256 ^ 16 := by simpa using h1
        omega
      · rw [two128_eq]; simpa using h2
      · simp [hl]
      · rw [two64_eq]; simpa using h4
  · cases h

theorem split4 (A B C D : Bytes) (hA : A.length = 16) (hB : B.length = 16) (hC : C.length = 32) :
    (A ++ B ++ C ++ D).take 16 = A ∧ ((A ++ B ++ C ++ D).drop 16).take 16 = B ∧
      ((A ++ B ++ C ++ D).drop 32).take 32 = C ∧ (A ++ B ++ C ++ D).drop 64 = D := by
  simp only [List.append_assoc]
  have d16 : (A ++ (B ++ (C ++ D))).drop 16 = B ++ (C ++ D) := List.drop_left' hA
  have d32 : (A ++ (B ++ (C ++ D))).drop 32 = C ++ D := by
    rw [show 32 = 16 + 16 from rfl, ← List.drop_drop, d16]; exact List.drop_left' hB
  have d64 : (A ++ (B ++ (C ++ D))).drop 64 = D := by
    rw [show 64 = 32 + 32 from rfl, ← List.drop_drop, d32]; exact List.drop_left' hC
  refine ⟨List.take_left' hA, ?_, ?_, d64⟩
  · rw [d16]; exact List.take_left' hB
  · rw [d32]; exact List.take_left' hC

theorem decode_encode (a : Account) (h1 : a.amount < Params.u128Max) (h2 : a.locked < Params.two128)
    (h3 : a.codeHash.length = 32) (h4 : a.storageUsage < Params.two64) :
    Account.decode (Account.encode a) = some a := by
  have e1 : a.amount < 256 ^ 16 := by have := u128Max_eq; rw [two128_eq] at this; omega
  have e2 : a.locked < 256 ^ 16 := by rw [← two128_eq]; exact h2
  have e4 : a.storageUsage < 256 ^ 8 := by rw [← two64_eq]; exact h4
  have l1 := leN_length 16 a.amount
  have l2 := leN_length 16 a.locked
  have l4 := leN_length 8 a.storageUsage
  have hlen : (Account.encode a).length = 72 := by
    simp only [Account.encode, u128, u64, List.length_append, l1, l2, l4, h3]
  obtain ⟨t1, t2, t3, t4⟩ := split4 (leN 16 a.amount) (leN 16 a.locked) a.codeHash
    (leN 8 a.storageUsage) l1 l2 h3
  have hne : a.amount ≠ Params.u128Max := Nat.ne_of_lt h1
  unfold Account.decode
  simp only [hlen, ↓reduceIte]
  simp only [Account.encode, u128, u64] at t1 t2 t3 t4 ⊢
  simp only [t1, t2, t3, t4, leNat_leN _ _ e1, leNat_leN _ _ e2, leNat_leN _ _ e4, hne, ↓reduceIte]

/-! ## Flat amounts -/

theorem amtAt_fresh (e : Ext) (k : Nat) : ∀ r, (∀ r', r' < r → e.slot r' ≠ k) →
    e.amtAt k r = (e.acc0 k).amount
  | 0, _ => rfl
  | r + 1, h => by
    simp only [Ext.amtAt, h r (by omega), ↓reduceIte, Nat.add_zero]
    exact amtAt_fresh e k r (fun r' hr => h r' (by omega))

theorem amtAt_succ_self (e : Ext) (r : Nat) :
    e.amtAt (e.slot r) (r + 1) = e.amtAt (e.slot r) r + (e.rc r).deposit := by
  simp [Ext.amtAt]

theorem amtAt_succ_other (e : Ext) (r k : Nat) (h : e.slot r ≠ k) :
    e.amtAt k (r + 1) = e.amtAt k r := by
  simp [Ext.amtAt, h]

/-! ## Account keys -/

theorem nibbles_lt : ∀ (b : Bytes), ∀ y ∈ nibbles b, y < 16
  | [], _, h => by cases h
  | x :: b, y, h => by
    have hx : x.toNat < 256 := x.toNat_lt
    simp only [nibbles, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · omega
    · omega
    · exact nibbles_lt b y h

theorem nibbles_length : ∀ (b : Bytes), (nibbles b).length = 2 * b.length
  | [] => rfl
  | _ :: b => by simp only [nibbles, List.length_cons, nibbles_length b]; omega

theorem accountKeyPath_lt (id : Bytes) : ∀ y ∈ accountKeyPath id, y < 16 := nibbles_lt _

theorem accountKeyPath_length (id : Bytes) : (accountKeyPath id).length = 2 * (id.length + 1) := by
  simp [accountKeyPath, nibbles_length]

theorem inSlice_receiver_length {r : Receipt} (h : r.inSlice = true) : r.receiverId.length ≤ 64 := by
  simp only [Receipt.inSlice, Receipt.wf, AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.2.1.2

end ZkFormal.Near.Prune
