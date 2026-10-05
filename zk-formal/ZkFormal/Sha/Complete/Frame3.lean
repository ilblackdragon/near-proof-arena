import ZkFormal.Sha.Complete.Frame2

/-!
# ZkFormal.Sha.Complete.Frame3 — padding bytes and the length word
-/

namespace ZkFormal.Sha.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Gen ZkFormal.Sha.Layout ZkFormal.Sha.Table

/-- A padding byte strictly inside the padded message, before the length word. -/
theorem pad_mid (m : List Nat) (k : Nat) (h1 : m.length ≤ k) (h2 : k + 8 < (ArenaCore.SHA256.pad m).length) :
    (ArenaCore.SHA256.pad m).getD k 0 = if k = m.length then 128 else 0 := by
  rw [pad_byte m k (by omega), if_neg (by omega)]
  by_cases hk : k = m.length
  · simp [hk]
  · simp [hk, h2]

section
variable (f lst : Int) (p : Nat → Int)

/-- Byte `q` of round row `Rj` (`j < 4`) is byte `64b + 16j + q` of the padded message. -/
theorem zev_byteE (nx : Row) (M : Msg) (b j q : Nat) (hM : MOk M) (hb : b < nb M) (hj : j < 4)
    (hq : q < 16) :
    zev (renv (.round j (blkOf M b)) nx f lst p) (byteE q) =
      ((ArenaCore.SHA256.pad M.bytes).getD (64 * b + (16 * j + q)) 0 : Nat) := by
  unfold byteE
  rw [zev_bits_of _ _ (8 * (3 - q % 4)) 8 (fun b' => bit ((blkOf M b).W (4 * j + q / 4)) (8 * (3 - q % 4) + b'))
    (fun b' hb' => by
      rw [zev_c, renv_cur, rowCell_round, rc_W j _ (q / 4) _ (by omega) (by omega)]),
    nbits_bit, W_byte M b hM hb j q hj hq, blk_getD M b _ hb (by omega)]

theorem pad_length_nb (M : Msg) : (ArenaCore.SHA256.pad M.bytes).length = 64 * nb M := by
  rw [pad_len, nb_eq]

theorem fr_padbyte (cur nx : Row) (hc : CurRow cur) (j q : Nat) (hj : j < 4) (hq : q < 16) :
    zev (renv cur nx f lst p)
      (if 16 * j + q < 56 then
        .mul (.mul (E.c (colR j)) (E.not (E.c (colF q))))
          (E.sub (byteE q) (E.smul 128 (.mul (E.c colP80) (dropE q))))
      else
        .mul (.mul (E.c (colR j)) (E.not (E.c (colF q))))
          (E.sub (.mul (E.not (E.c colLast)) (byteE q)) (E.smul 128 (.mul (E.c colPn) (dropE q))))) = 0 := by
  have hdrop : ∀ M b, zev (renv (.round j (blkOf M b)) nx f lst p) (dropE q) =
      (((if q = 0 then (if j = 0 then 1 else if j < 4 ∧ 64 * b + (16 * j - 1) < M.bytes.length then 1 else 0)
        else (if j < 4 ∧ 64 * b + (16 * j + (q - 1)) < M.bytes.length then 1 else 0) : Nat) : Int)) -
      (((if j < 4 ∧ 64 * b + (16 * j + q) < M.bytes.length then 1 else 0 : Nat)) : Int) := by
    intro M b
    unfold dropE
    split
    · simp only [zev_sub, zev_c, renv_cur, rowCell_round, r_Fprev, r_F M b j q hq]
    · simp only [zev_sub, zev_c, renv_cur, rowCell_round, r_F M b j q hq, r_F M b j (q - 1) (by omega)]
  split
  · apply cur_round' f lst p cur nx hc j (by omega)
    intro M b hM hb
    have hn := blk_arith M b hb
    have hpl := pad_length_nb M
    simp only [zev_mul, zev_not, zev_sub, zev_smul, zev_c, renv_cur, rowCell_round, r_F M b j q hq, r_P80,
      hdrop M b, zev_byteE f lst p nx M b j q hM hb hj hq]
    by_cases hd : 64 * b + (16 * j + q) < M.bytes.length
    · rw [if_pos ⟨hj, hd⟩]; omega
    · rw [pad_mid _ _ (by omega) (by omega)]
      ites
  · apply cur_round' f lst p cur nx hc j (by omega)
    intro M b hM hb
    have hn := blk_arith M b hb
    have hpl := pad_length_nb M
    simp only [zev_mul, zev_not, zev_sub, zev_smul, zev_c, renv_cur, rowCell_round, r_F M b j q hq, r_Last,
      r_Pn, hdrop M b, zev_byteE f lst p nx M b j q hM hb hj hq]
    by_cases hd : 64 * b + (16 * j + q) < M.bytes.length
    · rw [if_pos ⟨hj, hd⟩]; omega
    · by_cases hl : b + 1 = nb M
      · rw [if_pos hl]
        ites
      · rw [pad_mid _ _ (by omega) (by omega)]
        ites

/-- The last block ends with the 64-bit length: words 14, 15 are `0`, `8·len`. -/
theorem last_words (M : Msg) (b : Nat) (hM : MOk M) (hb : b < nb M) (hlast : b + 1 = nb M) :
    (blkOf M b).W 14 = 0 ∧ (blkOf M b).W 15 = 8 * M.bytes.length := by
  have hn := nb_eq M
  have hpl := pad_length_nb M
  have hL := hM.len
  have hbyte : ∀ r, r < 8 → (blkOf M b).blk.getD (56 + r) 0 = 8 * M.bytes.length / 256 ^ (7 - r) % 256 := by
    intro r hr
    rw [blk_getD M b _ hb (by omega), pad_byte _ _ (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    congr 3
    omega
  unfold Blk.W
  rw [Spec.Wt_lt16 _ (words16 M b hb) _ (by decide), Spec.Wt_lt16 _ (words16 M b hb) _ (by decide),
    words_getD _ _ (by rw [blk_length M b hb]; decide), words_getD _ _ (by rw [blk_length M b hb]; decide)]
  have h0 := hbyte 0 (by decide); have h1 := hbyte 1 (by decide)
  have h2 := hbyte 2 (by decide); have h3 := hbyte 3 (by decide)
  have h4 := hbyte 4 (by decide); have h5 := hbyte 5 (by decide)
  have h6 := hbyte 6 (by decide); have h7 := hbyte 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.pow_zero] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  constructor <;> omega

theorem fr_len14 (cur nx : Row) (hc : CurRow cur) (k : Nat) (hk : k < 32) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c (colW 2 k))) = 0 := by
  apply cur_round' f lst p cur nx hc 3 (by decide)
  intro M b hM hb
  simp only [zev_mul, zev_c, renv_cur, rowCell_round, r_Last, rc_W 3 _ 2 k (by decide) hk]
  split
  · next hl =>
    rw [(last_words M b hM hb hl).1]
    simp [bit]
  · simp

theorem fr_len15 (cur nx : Row) (hc : CurRow cur) (k : Nat) (hk1 : 28 ≤ k) (hk : k < 32) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 3)) (E.c colLast)) (E.c (colW 3 k))) = 0 := by
  apply cur_round' f lst p cur nx hc 3 (by decide)
  intro M b hM hb
  simp only [zev_mul, zev_c, renv_cur, rowCell_round, r_Last, rc_W 3 _ 3 k (by decide) hk]
  split
  · next hl =>
    rw [(last_words M b hM hb hl).2]
    have hL := hM.len
    have : bit (8 * M.bytes.length) k = 0 := by
      rw [bit_eq, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show 8 * M.bytes.length < 2 ^ 28 by omega)
        (Nat.pow_le_pow_right (by decide) hk1))]
      rfl
    rw [this]; simp
  · simp

theorem fr_lenNd (cur nx : Row) (hc : CurRow cur) :
    zev (renv cur nx f lst p) (.mul (.mul (E.c (colR 3)) (E.c colLast))
      (E.sub (E.bits (fun b => E.c (colW 3 b)) 0 28) (E.smul 8 (E.c colNd)))) = 0 := by
  apply cur_round' f lst p cur nx hc 3 (by decide)
  intro M b hM hb
  have hn := blk_arith M b hb
  rw [zev_mul, zev_sub, zev_bits_of _ _ 0 28 (fun k => bit ((blkOf M b).W 15) (0 + k)) (fun k hk => by
    rw [zev_c, renv_cur, rowCell_round, rc_W 3 _ 3 _ (by decide) (by omega)]), nbits_bit]
  simp only [zev_c, zev_smul, renv_cur, rowCell_round, r_Last, r_Nd]
  split
  · next hl =>
    rw [(last_words M b hM hb hl).2]
    have hL := hM.len
    simp only [Nat.pow_zero, Nat.div_one]
    omega
  · simp
end

end ZkFormal.Sha.Complete
