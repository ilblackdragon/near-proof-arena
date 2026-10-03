import ReexecNpai.Spec.RecAux6

/-!
# Record parse: byte-level helpers
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

theorem sl_add (pb : Bytes) (a n1 n2 : Nat) : sl pb a (n1 + n2) = sl pb a n1 ++ sl pb (a + n1) n2 := by
  simp only [sl, List.take_add, List.drop_drop]

theorem sl_cons (pb : Bytes) (a n : Nat) (h : a < pb.length) :
    sl pb a (n + 1) = pb[a] :: sl pb (a + 1) n := by
  rw [Nat.add_comm, sl_add]
  simp only [sl, List.drop_eq_getElem_cons h, List.take_succ_cons, List.take_zero]
  rfl

theorem sl_one_zero (pb : Bytes) (a : Nat) (h : a < pb.length) (hz : u8At pb a = 0) : sl pb a 1 = [0] := by
  rw [sl_cons pb a 0 h]
  simp only [sl, List.take_zero, List.cons.injEq, and_true]
  apply UInt8.toNat_inj.mp
  simp [u8At, List.getElem?_eq_getElem h] at hz
  simpa using hz

theorem u32_sl (pb : Bytes) (a : Nat) (h : a + 4 ≤ pb.length) : u32 (leAt pb a 4) = sl pb a 4 := by
  have hl : (sl pb a 4).length = 4 := sl_length_of h
  have := leN_leNat (sl pb a 4)
  rw [hl] at this
  exact this

theorem u64_sl (pb : Bytes) (a : Nat) (h : a + 8 ≤ pb.length) : u64 (leAt pb a 8) = sl pb a 8 := by
  have hl : (sl pb a 8).length = 8 := sl_length_of h
  have := leN_leNat (sl pb a 8)
  rw [hl] at this
  exact this

theorem u16_sl (pb : Bytes) (a : Nat) (h : a + 2 ≤ pb.length) : u16 (leAt pb a 2) = sl pb a 2 := by
  have hl : (sl pb a 2).length = 2 := sl_length_of h
  have := leN_leNat (sl pb a 2)
  rw [hl] at this
  exact this

theorem leAt_lt (pb : Bytes) (a w : Nat) : leAt pb a w < 256 ^ w := by
  have := leNat_lt (sl pb a w)
  have hl : (sl pb a w).length ≤ w := by rw [sl_length]; exact Nat.min_le_left _ _
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hl)

theorem leAt4_lt (pb : Bytes) (a : Nat) : leAt pb a 4 < 4294967296 := by
  have := leAt_lt pb a 4; simpa using this

theorem leAt8_lt (pb : Bytes) (a : Nat) : leAt pb a 8 < 18446744073709551616 := by
  have := leAt_lt pb a 8; simpa using this

theorem leAt2_lt (pb : Bytes) (a : Nat) : leAt pb a 2 < 65536 := by
  have := leAt_lt pb a 2; simpa using this

theorem pseg_PF (pb : Bytes) (a n : Nat) : pseg pb (PF + a) n = sl pb a n := by
  simp [pseg, sl]

theorem keyOfHP_sl (leaf : Bool) (pb : Bytes) (a n : Nat) (hn : 1 ≤ n) (ha : a + n ≤ pb.length) :
    (∃ k, keyOfHP leaf (sl pb a n) = some k) ↔
      (u8At pb a = (if leaf then 32 else 0) ∨
        ((16 + (if leaf then 32 else 0)) ≤ u8At pb a ∧ u8At pb a < 32 + (if leaf then 32 else 0))) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [sl_cons pb a n' (by omega)]
  have hb : (pb[a]'(by omega)).toNat = u8At pb a := by
    simp [u8At, List.getElem?_eq_getElem (show a < pb.length by omega)]
  simp only [keyOfHP, hb]
  by_cases c1 : u8At pb a = (if leaf then 32 else 0)
  · simp [c1]
  · by_cases c2 : (16 + (if leaf then 32 else 0)) ≤ u8At pb a ∧ u8At pb a < 32 + (if leaf then 32 else 0)
    · simp only [c1, ↓reduceIte, c2, and_self, false_or, iff_true]; exact ⟨_, rfl⟩
    · simp only [c1, ↓reduceIte, c2, false_or, iff_false]
      intro ⟨k, hk⟩; simp at hk

theorem u8At_lt (pb : Bytes) (a : Nat) : u8At pb a < 256 := (pb[a]?.getD 0).toNat_lt

end ReexecNpai
