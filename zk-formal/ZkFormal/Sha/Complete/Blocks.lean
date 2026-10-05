import ZkFormal.Sha.Complete.Kind

/-!
# ZkFormal.Sha.Complete.Blocks — facts about the generator's blocks

For `B = blkOf M b` (`b < nb M`): 64 bytes `< 256`, 16 schedule words, all
words `< 2^32`, and the chaining value of block `b+1` is `compress` of block
`b` (so equals the digest row's `hout`).
-/

namespace ZkFormal.Sha.Complete

open ArenaCore ArenaCore.SHA256 ZkFormal.Sha.Spec ZkFormal.Sha.Gen

def W32 (l : List Nat) : Prop := ∀ x ∈ l, x < 2 ^ 32

theorem getD_lt {l : List Nat} (h : W32 l) (i : Nat) : l.getD i 0 < 2 ^ 32 := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hl)

theorem compress_w32 (h blk : List Nat) : W32 (compress h blk) := by
  intro x hx
  simp only [compress, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact add32_lt _ _

theorem H0_w32 : W32 H0 := by
  intro x hx
  simp only [H0, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem foldl_compress_w32 (bs : List (List Nat)) (h : List Nat) (hh : W32 h) :
    W32 (bs.foldl compress h) := by
  induction bs generalizing h with
  | nil => exact hh
  | cons b bs ih => exact ih _ (compress_w32 _ _)

theorem foldl_compress_len (bs : List (List Nat)) (h : List Nat) (hh : h.length = 8) :
    (bs.foldl compress h).length = 8 := by
  induction bs generalizing h with
  | nil => exact hh
  | cons b bs ih => exact ih _ rfl

/-! ## Padding and chunks -/

theorem pad_length (m : List Nat) : (pad m).length = 64 * ((pad m).length / 64) := by
  simp only [pad, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    List.length_map, Bytes.beN_length]
  omega

theorem pad_bytes (m : List Nat) (hm : ∀ x ∈ m, x < 256) : ∀ x ∈ pad m, x < 256 := by
  intro x hx
  simp only [pad, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_replicate,
    List.mem_map] at hx
  rcases hx with ((h | h) | h) | ⟨y, -, rfl⟩
  · exact hm x h
  · subst h; decide
  · rw [h.2]; decide
  · exact y.toNat_lt

theorem chunks_length (n : Nat) (l : List Nat) : (chunks n l).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => simp [chunks, ih]

theorem chunks_mem (n : Nat) (l : List Nat) : ∀ c ∈ chunks n l, ∀ x ∈ c, x ∈ l := by
  induction n generalizing l with
  | zero => intro c hc; simp [chunks] at hc
  | succ n ih =>
    intro c hc x hx
    simp only [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop (ih _ c hc x hx)

theorem chunks_len64 (n : Nat) (l : List Nat) (hl : l.length = 64 * n) :
    ∀ c ∈ chunks n l, c.length = 64 := by
  induction n generalizing l with
  | zero => intro c hc; simp [chunks] at hc
  | succ n ih =>
    intro c hc
    simp only [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp [hl]; omega
    · exact ih _ (by simp [hl]; omega) c hc

/-! ## Blocks of a message -/

variable (M : Msg) (b : Nat)

theorem blk_mem (hb : b < nb M) : (blkOf M b).blk ∈ msgBlocks M.bytes := by
  show (msgBlocks M.bytes).getD b [] ∈ _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

theorem blk_length (hb : b < nb M) : (blkOf M b).blk.length = 64 :=
  chunks_len64 _ _ (pad_length _) _ (blk_mem M b hb)

theorem blk_bytes (hM : MOk M) (hb : b < nb M) : ∀ x ∈ (blkOf M b).blk, x < 256 :=
  fun x hx => pad_bytes _ hM.bytes x (chunks_mem _ _ _ (blk_mem M b hb) x hx)

theorem words_lt : ∀ n (l : List Nat), l.length ≤ n → (∀ x ∈ l, x < 256) → W32 (words l) := by
  intro n
  induction n with
  | zero => intro l hl _; match l, hl with | [], _ => intro x hx; simp [words] at hx
  | succ n ih =>
    intro l hl h256
    match l with
    | a :: b :: c :: d :: rest =>
      intro x hx
      simp only [words, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have ha := h256 a (by simp); have hb := h256 b (by simp)
        have hc := h256 c (by simp); have hd := h256 d (by simp)
        omega
      · exact ih rest (by simp at hl; omega) (fun y hy => h256 y (by simp [hy])) x hx
    | [] => intro x hx; simp [words] at hx
    | [_] => intro x hx; simp [words] at hx
    | [_, _] => intro x hx; simp [words] at hx
    | [_, _, _] => intro x hx; simp [words] at hx

theorem words16 (hb : b < nb M) : (words (blkOf M b).blk).length = 16 :=
  words_length_16 _ (blk_length M b hb)

theorem W_lt (hM : MOk M) (hb : b < nb M) (t : Nat) : (blkOf M b).W t < 2 ^ 32 := by
  unfold Blk.W
  by_cases ht : t < 16
  · rw [Wt_lt16 _ (words16 M b hb) t ht]
    exact getD_lt (words_lt _ _ (Nat.le_refl _) (blk_bytes M b hM hb)) t
  · rw [show t = (t - 16) + 16 by omega, Wt_rec' _ (words16 M b hb)]
    exact Nat.mod_lt _ (by decide)

theorem hin_w32 : W32 (blkOf M b).hin := foldl_compress_w32 _ _ H0_w32

theorem hin_len : (blkOf M b).hin.length = 8 := foldl_compress_len _ _ rfl

theorem Rs_lt (h blk : List Nat) (hh : W32 h) :
    ∀ t, (Rs h blk t).a < 2 ^ 32 ∧ (Rs h blk t).e < 2 ^ 32
  | 0 => ⟨getD_lt hh 0, getD_lt hh 4⟩
  | _ + 1 => ⟨add32_lt _ _, add32_lt _ _⟩

theorem As_lt (h blk : List Nat) (hh : W32 h) (u : Nat) : As h blk u < 2 ^ 32 := by
  match u with
  | 0 => exact getD_lt hh 3
  | 1 => exact getD_lt hh 2
  | 2 => exact getD_lt hh 1
  | u + 3 => exact (Rs_lt h blk hh u).1

theorem Es_lt (h blk : List Nat) (hh : W32 h) (u : Nat) : Es h blk u < 2 ^ 32 := by
  match u with
  | 0 => exact getD_lt hh 7
  | 1 => exact getD_lt hh 6
  | 2 => exact getD_lt hh 5
  | u + 3 => exact (Rs_lt h blk hh u).2

theorem A_lt (u : Nat) : (blkOf M b).A u < 2 ^ 32 := As_lt _ _ (hin_w32 M b) u
theorem E_lt (u : Nat) : (blkOf M b).Ee u < 2 ^ 32 := Es_lt _ _ (hin_w32 M b) u

theorem hout_lt (w : Nat) : (blkOf M b).hout w < 2 ^ 32 := add32_lt _ _

theorem hin_zero : (blkOf M 0).hin = H0 := rfl

theorem hin_succ (hb : b < nb M) :
    (blkOf M (b + 1)).hin = compress (blkOf M b).hin (blkOf M b).blk := by
  show ((msgBlocks M.bytes).take (b + 1)).foldl compress H0 =
    compress (((msgBlocks M.bytes).take b).foldl compress H0) ((msgBlocks M.bytes).getD b [])
  rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem hb,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  rfl

theorem compress_getD (B : Blk) (w : Nat) (hw : w < 8) :
    (compress B.hin B.blk).getD w 0 = B.hout w := by
  rw [compress_eq]
  unfold Blk.hout Blk.fin Blk.A Blk.Ee
  match w, hw with
  | 0, _ => simp only [List.getD_cons_zero]; rw [if_pos (by decide)]
  | 1, _ => simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [if_pos (by decide)]
  | 2, _ => simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [if_pos (by decide)]
  | 3, _ => simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [if_pos (by decide)]
  | 4, _ => simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [if_neg (by decide)]
  | 5, _ => simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [if_neg (by decide)]
  | 6, _ => simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [if_neg (by decide)]
  | 7, _ => simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [if_neg (by decide)]

theorem hin_succ_getD (hb : b < nb M) (w : Nat) (hw : w < 8) :
    (blkOf M (b + 1)).hin.getD w 0 = (blkOf M b).hout w := by
  rw [hin_succ M b hb, compress_getD _ w hw]

theorem ivW_lt (w : Nat) : ivW w < 2 ^ 32 := getD_lt H0_w32 w

/-! ## Initial window -/

/-- The first four `a`s and `e`s of a block are its chaining value. -/
theorem A_init (B : Blk) (u : Nat) (hu : u < 4) : B.A u = B.hin.getD (3 - u) 0 := by
  unfold Blk.A
  match u, hu with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem E_init (B : Blk) (u : Nat) (hu : u < 4) : B.Ee u = B.hin.getD (7 - u) 0 := by
  unfold Blk.Ee
  match u, hu with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

end ZkFormal.Sha.Complete
