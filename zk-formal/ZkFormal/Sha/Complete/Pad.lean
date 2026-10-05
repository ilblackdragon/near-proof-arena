import ZkFormal.Sha.Complete.Blocks

/-!
# ZkFormal.Sha.Complete.Pad — bytes of the padded message, bytes of words

* `nb_eq`: `64 · nb M` is the padded length `len + 9 + (119 - len % 64) % 64`;
* `pad_getD_*`: the byte at each position of `pad m`;
* `blk_getD`: byte `k` of block `b` is byte `64b + k` of `pad m`;
* `W_byte`: byte `q` of round row `Rj` (`j < 4`) is block byte `16j + q`.
-/

namespace ZkFormal.Sha.Complete

open ArenaCore ArenaCore.SHA256 ZkFormal.Sha.Spec ZkFormal.Sha.Gen

theorem pad_len (m : List Nat) :
    (pad m).length = m.length + 9 + (119 - m.length % 64) % 64 := by
  simp only [pad, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    List.length_map, Bytes.beN_length]
  omega

theorem nb_eq (M : Msg) : 64 * nb M = M.bytes.length + 9 + (119 - M.bytes.length % 64) % 64 := by
  unfold nb msgBlocks
  rw [chunks_length, ← pad_len]
  have := pad_length M.bytes
  omega

theorem getD_append_left' (l1 l2 : List Nat) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2).getD i 0 = l1.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l1 l2 : List Nat) (i : Nat) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i 0 = l2.getD (i - l1.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

section
variable (m : List Nat)

theorem pad_getD_data (i : Nat) (h : i < m.length) : (pad m).getD i 0 = m.getD i 0 := by
  unfold pad
  rw [List.append_assoc, List.append_assoc, getD_append_left' _ _ _ h]

theorem pad_getD_80 : (pad m).getD m.length 0 = 128 := by
  unfold pad
  rw [List.append_assoc, List.append_assoc, getD_append_right' _ _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

theorem pad_getD_zero (i : Nat) (h1 : m.length < i) (h2 : i < m.length + 1 + (119 - m.length % 64) % 64) :
    (pad m).getD i 0 = 0 := by
  unfold pad
  rw [List.append_assoc, List.append_assoc, getD_append_right' _ _ _ (by omega)]
  rw [show i - m.length = (i - m.length - 1) + 1 by omega, List.singleton_append, List.getD_cons_succ]
  have hr := List.length_replicate (n := (119 - m.length % 64) % 64) (a := 0)
  rw [getD_append_left' _ _ _ (by rw [hr]; omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem beN_getD (w x i : Nat) (hi : i < w) :
    ((Bytes.beN w x).map UInt8.toNat).getD i 0 = x / 256 ^ (w - 1 - i) % 256 := by
  induction w generalizing x i with
  | zero => omega
  | succ w ih =>
    simp only [Bytes.beN, List.map_append, List.map_cons, List.map_nil]
    by_cases h : i < w
    · rw [getD_append_left' _ _ _ (by simp [Bytes.beN_length]; omega), ih _ _ h,
        Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3 <;> omega
    · rw [getD_append_right' _ _ _ (by simp [Bytes.beN_length]; omega)]
      simp only [List.length_map, Bytes.beN_length, show i - w = 0 by omega, List.getD_cons_zero,
        show w + 1 - 1 - i = 0 by omega, Nat.pow_zero, Nat.div_one, UInt8.toNat_ofNat']
      exact Nat.mod_mod_of_dvd _ (by decide)

theorem pad_getD_len (i : Nat) (h1 : m.length + 1 + (119 - m.length % 64) % 64 ≤ i)
    (h2 : i < (pad m).length) :
    (pad m).getD i 0 = 8 * m.length / 256 ^ (7 - (i - (m.length + 1 + (119 - m.length % 64) % 64))) % 256 := by
  have hl := pad_len m
  unfold pad
  rw [getD_append_right' _ _ _ (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  rw [beN_getD 8 _ _ (by omega)]
end

theorem chunks_getD (n b : Nat) (l : List Nat) (hb : b < n) :
    (chunks n l).getD b [] = (l.drop (64 * b)).take 64 := by
  induction n generalizing b l with
  | zero => omega
  | succ n ih =>
    cases b with
    | zero => simp [chunks]
    | succ b =>
      simp only [chunks, List.getD_cons_succ]
      rw [ih b _ (by omega), List.drop_drop, show 64 + 64 * b = 64 * (b + 1) by omega]

theorem blk_getD (M : Msg) (b k : Nat) (hb : b < nb M) (hk : k < 64) :
    (blkOf M b).blk.getD k 0 = (pad M.bytes).getD (64 * b + k) 0 := by
  show ((msgBlocks M.bytes).getD b []).getD k 0 = _
  unfold nb msgBlocks at hb
  rw [chunks_length] at hb
  unfold msgBlocks
  rw [chunks_getD _ _ _ hb]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hk, List.getElem?_drop]

theorem words_getD : ∀ (m : Nat) (l : List Nat), 4 * m + 3 < l.length →
    (words l).getD m 0 =
      ((l.getD (4 * m) 0 * 256 + l.getD (4 * m + 1) 0) * 256 + l.getD (4 * m + 2) 0) * 256 +
        l.getD (4 * m + 3) 0
  | m, a :: b :: c :: d :: rest, h => by
    cases m with
    | zero => simp [words]
    | succ m =>
      have := words_getD m rest (by simp at h; omega)
      have e : ∀ n, (a :: b :: c :: d :: rest).getD (n + 4) 0 = rest.getD n 0 := fun n => by
        simp only [List.getD_cons_succ]
      have e0 : (words (a :: b :: c :: d :: rest)).getD (m + 1) 0 = (words rest).getD m 0 := by
        simp only [words, List.getD_cons_succ]
      rw [e0, show 4 * (m + 1) = 4 * m + 4 by omega, show 4 * m + 4 + 1 = (4 * m + 1) + 4 by omega,
        show 4 * m + 4 + 2 = (4 * m + 2) + 4 by omega, show 4 * m + 4 + 3 = (4 * m + 3) + 4 by omega,
        e, e, e, e, this]
  | m, [], h => by simp at h
  | m, [_], h => by simp at h <;> omega
  | m, [_, _], h => by simp at h <;> omega
  | m, [_, _, _], h => by simp at h <;> omega

theorem getD_lt256 (l : List Nat) (h : ∀ x ∈ l, x < 256) (i : Nat) : l.getD i 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hl)

/-- Byte `q` of round row `Rj` (`j < 4`) is byte `16j + q` of the block. -/
theorem W_byte (M : Msg) (b : Nat) (hM : MOk M) (hb : b < nb M) (j q : Nat) (hj : j < 4) (hq : q < 16) :
    (blkOf M b).W (4 * j + q / 4) / 2 ^ (8 * (3 - q % 4)) % 2 ^ 8 = (blkOf M b).blk.getD (16 * j + q) 0 := by
  unfold Blk.W
  rw [Wt_lt16 _ (words16 M b hb) _ (by omega), words_getD _ _ (by rw [blk_length M b hb]; omega)]
  have hB := getD_lt256 _ (blk_bytes M b hM hb)
  have h0 := hB (4 * (4 * j + q / 4))
  have h1 := hB (4 * (4 * j + q / 4) + 1)
  have h2 := hB (4 * (4 * j + q / 4) + 2)
  have h3 := hB (4 * (4 * j + q / 4) + 3)
  have hr : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr <;> rw [hr]
  · rw [show 16 * j + q = 4 * (4 * j + q / 4) by omega]; omega
  · rw [show 16 * j + q = 4 * (4 * j + q / 4) + 1 by omega]; omega
  · rw [show 16 * j + q = 4 * (4 * j + q / 4) + 2 by omega]; omega
  · rw [show 16 * j + q = 4 * (4 * j + q / 4) + 3 by omega]; omega

/-- Byte at position `k` of the padded message, by region. -/
theorem pad_byte (m : List Nat) (k : Nat) (hk : k < (pad m).length) :
    (pad m).getD k 0 =
      if k < m.length then m.getD k 0
      else if k = m.length then 128
      else if k + 8 < (pad m).length then 0
      else 8 * m.length / 256 ^ ((pad m).length - 1 - k) % 256 := by
  have hl := pad_len m
  split
  · exact pad_getD_data m k (by assumption)
  · split
    · next h => rw [h]; exact pad_getD_80 m
    · split
      · exact pad_getD_zero m k (by omega) (by omega)
      · rw [pad_getD_len m k (by omega) hk]
        congr 3 <;> omega

end ZkFormal.Sha.Complete
