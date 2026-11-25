import StateM5a.WsBridge
import StateM5a.Stc

/-!
# StateM5a.StcBytes — B-T3: the byte-level facts behind the `STC` opening (no trace)

* `beN_beToNat`: big-endian decoding is inverted by encoding at the list's length;
* `chunk` / `wordOf`: word `w` of a byte function `f` (its bytes `8w … 8w+7`, big-endian);
  **`wbytes_words`**: the bytes of `n` consecutive words are the byte function on `8n` positions;
* **`limbs_word`**: the chip limbs of a word whose bytes are `b₀ … b₇` with byte 5 = `lo5 + 32·hi3`
  and byte 2 = `lo2 + 4·hi6` are `Stc.wordW`'s three limb sums;
* **`sha384_stc`**: SHA-384 of a 139-byte message is `toB` of the first 6 words of the two-block
  compression chain over the padded message's 32 words (`Stc.padByte` is FIPS padding);
* `limb3` bytes, `u64` of a 3-byte count.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.StcBytes

open ArenaCore.Bytes NearSpecV3 StateM5a.WsBridge StateM5a.Sha512If
open StateM5a.StateView (wbytes)

abbrev Bytes := ArenaCore.Bytes

theorem toNat_ofNat_lt {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  simp [Nat.mod_eq_of_lt h]

theorem beN_add_mul : ∀ (w n x : Nat), beN w (n + 256 ^ w * x) = beN w n
  | 0, _, _ => rfl
  | w + 1, n, x => by
    simp only [beN]
    have e : 256 ^ (w + 1) * x = 256 * (256 ^ w * x) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ w) 256, Nat.mul_assoc]
    rw [e, show (n + 256 * (256 ^ w * x)) / 256 = n / 256 + 256 ^ w * x by omega,
      show (n + 256 * (256 ^ w * x)) % 256 = n % 256 by omega, beN_add_mul w]

theorem beN_succ_cons : ∀ (w n : Nat), beN (w + 1) n = UInt8.ofNat (n / 256 ^ w % 256) :: beN w n
  | 0, n => by simp [beN]
  | w + 1, n => by
    rw [beN, beN_succ_cons w (n / 256), beN]
    simp only [List.cons_append, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem beToNat_cons (x : UInt8) (l : Bytes) : beToNat (x :: l) = x.toNat * 256 ^ l.length + beToNat l := by
  have gen : ∀ (l : Bytes) (acc : Nat), l.foldl (fun acc x => acc * 256 + x.toNat) acc =
      acc * 256 ^ l.length + l.foldl (fun acc x => acc * 256 + x.toNat) 0 := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons y r ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, ih (0 * 256 + y.toNat), Nat.pow_succ]
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256, Nat.add_assoc]
  simp only [beToNat, List.foldl_cons]
  rw [gen]; simp

theorem beToNat_lt : ∀ l : Bytes, beToNat l < 256 ^ l.length
  | [] => by simp [beToNat]
  | x :: l => by
    rw [beToNat_cons, List.length_cons, Nat.pow_succ]
    have hx : x.toNat + 1 ≤ 256 := x.toNat_lt
    have h1 := beToNat_lt l
    have h2 : (x.toNat + 1) * 256 ^ l.length ≤ 256 * 256 ^ l.length := Nat.mul_le_mul_right _ hx
    rw [Nat.succ_mul, Nat.mul_comm 256] at h2
    omega

theorem beN_beToNat : ∀ l : Bytes, beN l.length (beToNat l) = l
  | [] => rfl
  | x :: l => by
    have hl := beToNat_lt l
    have hx := x.toNat_lt
    rw [List.length_cons, beN_succ_cons, beToNat_cons, Nat.add_comm, Nat.mul_comm, beN_add_mul,
      beN_beToNat l]
    congr 1
    rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 256)), Nat.div_eq_of_lt hl, Nat.zero_add,
      Nat.mod_eq_of_lt hx, UInt8.ofNat_toNat]

/-! ## Words of a byte function -/

/-- The 8 big-endian bytes of word `w`. -/
def chunk (f : Nat → Nat) (w : Nat) : Bytes := (List.range 8).map fun j => UInt8.ofNat (f (8 * w + j))

/-- Word `w` of the byte function `f`. -/
def wordOf (f : Nat → Nat) (w : Nat) : Nat := beToNat (chunk f w)

/-- Words `w0 … w0 + n − 1`. -/
def wordsF (f : Nat → Nat) (w0 n : Nat) : List Nat := (List.range n).map fun i => wordOf f (w0 + i)

theorem chunk_length (f : Nat → Nat) (w : Nat) : (chunk f w).length = 8 := by simp [chunk]

theorem wordOf_lt (f : Nat → Nat) (w : Nat) : wordOf f w < 2 ^ 64 := by
  have := beToNat_lt (chunk f w); rw [chunk_length] at this; unfold wordOf; simpa using this

theorem beN_wordOf (f : Nat → Nat) (w : Nat) : beN 8 (wordOf f w) = chunk f w := by
  have := beN_beToNat (chunk f w); rwa [chunk_length] at this

theorem range_flatMap8 {α : Type} (g : Nat → α) : ∀ n,
    (List.range n).flatMap (fun i => (List.range 8).map fun j => g (8 * i + j)) =
      (List.range (8 * n)).map g
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ (n := n), List.flatMap_append, range_flatMap8 g n, show 8 * (n + 1) = 8 * n + 8 by omega,
      List.range_add, List.map_append, List.map_map]
    simp [Function.comp_def]

/-- **The bytes of consecutive words.** -/
theorem wbytes_words (f : Nat → Nat) (hf : ∀ p, f p < 256) (w0 n : Nat) :
    wbytes (wordsF f w0 n) = (List.range (8 * n)).map fun p => f (8 * w0 + p) := by
  rw [← range_flatMap8]
  simp only [wbytes, wordsF, List.flatMap_map]
  congr 1; funext i
  rw [beN_wordOf, chunk, List.map_map]
  apply List.map_congr_left; intro j _
  simp only [Function.comp, toNat_ofNat_lt (hf _)]
  congr 1; omega

/-- `toB` of a digest whose words are `wordsF f 0 6`. -/
theorem toB_words (f : Nat → Nat) (h6 : (wordsF f 0 6).length = 6 ∧ W64 (wordsF f 0 6)) :
    toB ⟨wordsF f 0 6, h6⟩ = (List.range 48).map fun p => UInt8.ofNat (f p) := by
  simp only [toB, wordsF, List.flatMap_map, Nat.zero_add, beN_wordOf]
  exact range_flatMap8 (fun p => UInt8.ofNat (f p)) 6

/-! ## The chip limbs of a word -/

/-- **A word's limbs from its bytes and split parts.** -/
theorem limbs_word (b0 b1 b2 b3 b4 b5 b6 b7 l5 h3 l2 h6 : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) (hb4 : b4 < 256)
    (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) (hl5 : l5 < 32) (hl2 : l2 < 4)
    (e5 : b5 = l5 + 32 * h3) (e2 : b2 = l2 + 4 * h6) :
    wlimbs (beToNat ([b0, b1, b2, b3, b4, b5, b6, b7].map UInt8.ofNat)) =
      [b7 + 256 * b6 + 65536 * l5, h3 + 8 * b4 + 2048 * b3 + 524288 * l2, h6 + 64 * b1 + 16384 * b0] := by
  simp only [List.map_cons, List.map_nil, beToNat, List.foldl, toNat_ofNat_lt h0, toNat_ofNat_lt h1,
    toNat_ofNat_lt hb2, toNat_ofNat_lt hb3, toNat_ofNat_lt hb4, toNat_ofNat_lt hb5, toNat_ofNat_lt hb6,
    toNat_ofNat_lt hb7, wlimbs]
  subst e5 e2
  refine List.cons_eq_cons.2 ⟨by omega, List.cons_eq_cons.2 ⟨by omega, List.cons_eq_cons.2 ⟨by omega, rfl⟩⟩⟩

/-! ## SHA-384 of the 139-byte message -/

theorem padTail : ((List.range 117).map fun i => Stc.padByte (139 + i)) =
    [0x80] ++ List.replicate 100 0 ++ (beN 16 (8 * 139)).map UInt8.toNat := by decide

/-- **The padded message** is the byte function on 256 positions. -/
theorem pad_stc (f : Nat → Nat) (hpad : ∀ p, 139 ≤ p → p < 256 → f p = Stc.padByte p) :
    SHA512.pad ((List.range 139).map f) = (List.range 256).map f := by
  have hk : (239 - ((List.range 139).map f).length % 128) % 128 = 100 := by simp
  simp only [SHA512.pad, List.length_map, List.length_range]
  rw [show (256 : Nat) = 139 + 117 from rfl, List.range_add, List.map_append, List.map_map, List.append_assoc,
    List.append_assoc]
  congr 1
  have : ((List.range 117).map (f ∘ (139 + ·))) = (List.range 117).map fun i => Stc.padByte (139 + i) := by
    apply List.map_congr_left; intro i hi
    have := List.mem_range.1 hi
    simp only [Function.comp_apply]
    exact hpad (139 + i) (by omega) (by omega)
  rw [this, padTail, List.append_assoc]

theorem blocks_two (h msg : List Nat) (hl : msg.length = 256) :
    SHA512.blocks 2 h msg = SHA512.compress (SHA512.compress h (msg.take 128)) (msg.drop 128) := by
  cases msg with
  | nil => simp at hl
  | cons x r =>
    simp only [List.length_cons] at hl
    simp only [SHA512.blocks]
    split
    · next e => have := congrArg List.length e; simp at this; omega
    · rw [List.take_of_length_le (l := List.drop 128 (x :: r)) (by simp; omega)]

theorem bnd_iv : NearSpecV3.E2E.Bnd.IV384 = StateM5a.IV384 := rfl

/-- **SHA-384 of the `STC` message**: the two-block compression chain over its 32 words. -/
theorem sha384_stc (f : Nat → Nat) (hf : ∀ p, f p < 256)
    (hpad : ∀ p, 139 ≤ p → p < 256 → f p = Stc.padByte p) :
    NearSpecV3.E2E.Bnd.sha384 ((List.range 139).map fun p => UInt8.ofNat (f p)) =
      toB (digest6 (cW (cW StateM5a.IV384 (wordsF f 0 16)) (wordsF f 16 16))) := by
  have hm : ((List.range 139).map fun p => UInt8.ofNat (f p)).map UInt8.toNat = (List.range 139).map f := by
    rw [List.map_map]; apply List.map_congr_left; intro p _; exact toNat_ofNat_lt (hf p)
  have hsplit : (List.range 256).map f = (List.range 128).map f ++ (List.range 128).map fun q => f (128 + q) := by
    rw [show (256 : Nat) = 128 + 128 from rfl, List.range_add, List.map_append, List.map_map]; rfl
  have hw1 : wbytes (wordsF f 0 16) = (List.range 128).map f := by
    rw [wbytes_words f hf]; rfl
  have hw2 : wbytes (wordsF f 16 16) = (List.range 128).map fun q => f (128 + q) := by
    rw [wbytes_words f hf]
  have hl : ((List.range 256).map f).length = 256 := by simp
  simp only [NearSpecV3.E2E.Bnd.sha384, hm, pad_stc f hpad, hl, Nat.reduceDiv, blocks_two _ _ hl]
  rw [hsplit, List.take_left' (by simp), List.drop_left' (by simp), ← toB_digest6]
  simp only [cW, hw1, hw2, bnd_iv]

/-! ## Digest limbs and the `u64` count -/

/-- A 42-B digest's 14 limbs (3 bytes each, big-endian) as bytes. -/
def limbBytes (l : List Nat) : Bytes :=
  l.flatMap fun x => [UInt8.ofNat (x / 65536 % 256), UInt8.ofNat (x / 256 % 256), UInt8.ofNat (x % 256)]

theorem range_flatMap3 {α : Type} (g : Nat → α) : ∀ n,
    (List.range n).flatMap (fun i => [g (3 * i), g (3 * i + 1), g (3 * i + 2)]) = (List.range (3 * n)).map g
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ (n := n), List.flatMap_append, range_flatMap3 g n, show 3 * (n + 1) = 3 * n + 3 by omega,
      List.range_add, List.map_append]
    simp [List.range_succ]

/-- **The limbs of bytes, read back.** -/
theorem limbBytes_limbs (g : Nat → Nat) (hg : ∀ j, j < 42 → g j < 256) :
    limbBytes ((List.range 14).map fun i => 65536 * g (3 * i) + 256 * g (3 * i + 1) + g (3 * i + 2)) =
      (List.range 42).map fun j => UInt8.ofNat (g j) := by
  rw [limbBytes, List.flatMap_map, show (42 : Nat) = 3 * 14 from rfl, ← range_flatMap3]
  unfold List.flatMap; congr 1; apply List.map_congr_left; intro i hi
  have hi := List.mem_range.1 hi
  have h0 := hg (3 * i) (by omega); have h1 := hg (3 * i + 1) (by omega); have h2 := hg (3 * i + 2) (by omega)
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> omega

theorem leN_leNat : ∀ l : Bytes, NearSpec.leN l.length (NearSpec.leNat l) = l
  | [] => rfl
  | x :: l => by
    have hx := x.toNat_lt
    simp only [List.length_cons, NearSpec.leN, NearSpec.leNat]
    rw [show (x.toNat + 256 * NearSpec.leNat l) % 256 = x.toNat by omega,
      show (x.toNat + 256 * NearSpec.leNat l) / 256 = NearSpec.leNat l by omega, leN_leNat l, UInt8.ofNat_toNat]

theorem leNat_lt : ∀ l : Bytes, NearSpec.leNat l < 256 ^ l.length
  | [] => by simp [NearSpec.leNat]
  | x :: l => by
    have hx := x.toNat_lt; have h := leNat_lt l
    simp only [NearSpec.leNat, List.length_cons, Nat.pow_succ]
    have : 256 * NearSpec.leNat l + 256 ≤ 256 * 256 ^ l.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    rw [Nat.mul_comm (256 ^ l.length)]; omega

/-- **The `u64` of a count `< 2^24`** from its three low bytes. -/
theorem u64_bytes (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    NearSpec.u64 (a + 256 * b + 65536 * c) = [a, b, c, 0, 0, 0, 0, 0].map UInt8.ofNat := by
  simp only [NearSpec.u64, NearSpec.leN, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega


end StateM5a.StcBytes
