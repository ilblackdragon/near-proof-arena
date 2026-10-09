import ZkFormal.NearV3.Extract.Ups.QNodes

/-!
# ZkFormal.NearV3.Extract.Ups.SpbSpec — the split branch `SPB`, spec side (layer 2)

`qSPB ci src cx x si v`: the branch a split part builds, by case (`ci` in `UCase.all` order,
`4 … 10` = `LSa LSb LSc ESl0 ESl1 ESn0 ESn1`), from the source record's node `src` (the leaf of
`LSa`, the extension of `ESl1`/`ESn1`), the moved node `cx` below (`LSb LSc ESl0 ESn0`: `MVL`/`MVE`
at `j = 1`), the record nibble `x`, the terminal row (`y = yOf si`) and the new value `v`.  These are
the branches of `splitLeaf` / `splitExt` before `wrapExt` (`qSPBleaf`, `qSPBext`), case by case.

Bitmap and hash list of `kids1` / `kids2` (`kids1_bm`, `kids2_bm`): one child at `x` gives `2^x` and
its hash; two children give `2^x + 2^y` and their hashes in slot order.
-/

namespace ZkFormal.NearV3.UpsSpec

open NearSpec

/-- The split branch of case `ci` (`qSPBleaf` / `qSPBext` before `wrapExt`). -/
def qSPB (ci : Nat) (src cx : PTrie) (x si : Nat) (v : Bytes) : PTrie :=
  match ci, src with
  | 4, .leaf _ sl _ => .branch (some sl) (kids1 (yOf si) (qNLF si v))
      (50 + valueMem sl.len + leafMem (ysOf si) v.length)
  | 5, _ => .branch (some (.val v)) (kids1 x cx) (50 + valueMem v.length + cx.memD)
  | 7, _ => .branch (some (.val v)) (kids1 x cx) (50 + valueMem v.length + cx.memD)
  | 6, _ => .branch none (kids2 x cx (yOf si) (qNLF si v)) (50 + cx.memD + leafMem (ysOf si) v.length)
  | 9, _ => .branch none (kids2 x cx (yOf si) (qNLF si v)) (50 + cx.memD + leafMem (ysOf si) v.length)
  | 8, .ext k c m => .branch (some (.val v)) (kids1 x c) (50 + valueMem v.length + (m - extOwnMem k))
  | 10, .ext k c m => .branch none (kids2 x c (yOf si) (qNLF si v))
      (50 + (m - extOwnMem k) + leafMem (ysOf si) v.length)
  | _, _ => .hash []

theorem kidsFrom_congr' : ∀ (n i : Nat) (f g : Nat → Option PTrie),
    (∀ x, i ≤ x → f x = g x) → kidsFrom n i f = kidsFrom n i g
  | 0, _, _, _, _ => rfl
  | n + 1, i, f, g, h => by
    simp only [kidsFrom, h i (Nat.le_refl _), kidsFrom_congr' n (i + 1) f g (fun x hx => h x (by omega))]

/-- No child in the range. -/
theorem kidsFrom0 : ∀ (n i : Nat) (f : Nat → Option PTrie), (∀ j, i ≤ j → f j = none) →
    kidsBitmap (kidsFrom n i f) i = 0 ∧ Kids.hashes (kidsFrom n i f) = []
  | 0, _, _, _ => by simp [kidsFrom, kidsBitmap, Kids.hashes]
  | n + 1, i, f, h => by
    have ih := kidsFrom0 n (i + 1) f (fun j hj => h j (by omega))
    simp only [kidsFrom, h i (Nat.le_refl _), kidsBitmap, Kids.hashes]
    exact ih

/-- One child (at `a`) in the range. -/
theorem kidsFrom1 (ca : PTrie) : ∀ (n i a : Nat) (f : Nat → Option PTrie), i ≤ a → a < i + n →
    (∀ j, i ≤ j → f j = if j = a then some ca else none) →
    kidsBitmap (kidsFrom n i f) i = 2 ^ a ∧ Kids.hashes (kidsFrom n i f) = ca.hashOf
  | 0, _, _, _, h1, h2, _ => by omega
  | n + 1, i, a, f, h1, h2, h => by
    by_cases hia : i = a
    · subst hia
      have z := kidsFrom0 n (i + 1) f (fun j hj => by rw [h j (by omega), if_neg (by omega)])
      simp only [kidsFrom, h i (Nat.le_refl _), ite_true, kidsBitmap, Kids.hashes, z.1, z.2]
      simp
    · have ih := kidsFrom1 ca n (i + 1) a f (by omega) (by omega) (fun j hj => h j (by omega))
      simp only [kidsFrom, h i (Nat.le_refl _), if_neg hia, kidsBitmap, Kids.hashes]
      exact ih

/-- Two children (at `a < b`) in the range. -/
theorem kidsFrom2 (ca cb : PTrie) : ∀ (n i a b : Nat) (f : Nat → Option PTrie), i ≤ a → a < b → b < i + n →
    (∀ j, i ≤ j → f j = if j = a then some ca else if j = b then some cb else none) →
    kidsBitmap (kidsFrom n i f) i = 2 ^ a + 2 ^ b ∧ Kids.hashes (kidsFrom n i f) = ca.hashOf ++ cb.hashOf
  | 0, _, _, _, _, h1, h2, h3, _ => by omega
  | n + 1, i, a, b, f, h1, h2, h3, h => by
    by_cases hia : i = a
    · subst hia
      have o := kidsFrom1 cb n (i + 1) b f (by omega) (by omega) (fun j hj => by
        rw [h j (by omega), if_neg (by omega)])
      simp only [kidsFrom, h i (Nat.le_refl _), ite_true, kidsBitmap, Kids.hashes, o.1, o.2]
      simp
    · have ih := kidsFrom2 ca cb n (i + 1) a b f (by omega) h2 (by omega) (fun j hj => h j (by omega))
      simp only [kidsFrom, h i (Nat.le_refl _), if_neg hia, show ¬ (i = b) by omega, ite_false, kidsBitmap,
        Kids.hashes]
      exact ih

theorem kids1_bm (x : Nat) (c : PTrie) (hx : x < 16) :
    kidsBitmap (kids1 x c) 0 = 2 ^ x ∧ Kids.hashes (kids1 x c) = c.hashOf :=
  kidsFrom1 c 16 0 x _ (Nat.zero_le _) (by omega) (fun _ _ => rfl)

theorem kids2_bm (x y : Nat) (c d : PTrie) (hx : x < 16) (hy : y < 16) (hxy : x ≠ y) :
    kidsBitmap (kids2 x c y d) 0 = 2 ^ x + 2 ^ y ∧
      Kids.hashes (kids2 x c y d) = if x < y then c.hashOf ++ d.hashOf else d.hashOf ++ c.hashOf := by
  unfold kids2
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · have := kidsFrom2 c d 16 0 x y _ (Nat.zero_le _) h (by omega) (fun _ _ => rfl)
    rw [if_pos h]; exact this
  · have := kidsFrom2 d c 16 0 y x (fun i => if i = x then some c else if i = y then some d else none)
      (Nat.zero_le _) h (by omega) (fun j _ => by
        by_cases h1 : j = y
        · subst h1; simp [show ¬ (j = x) by omega]
        · simp [h1])
    rw [if_neg (by omega), Nat.add_comm]; exact this

end ZkFormal.NearV3.UpsSpec
