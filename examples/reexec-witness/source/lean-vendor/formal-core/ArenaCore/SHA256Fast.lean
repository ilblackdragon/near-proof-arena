import ArenaCore.SHA256

/-!
# ArenaCore.SHA256Fast — a fast compiled SHA-256, proven equal to the spec

`ArenaCore.sha256` (`ArenaCore.SHA256`) is the specification: `Nat` words,
`List` message schedule, kernel-evaluable.  Compiled, it runs at roughly
40 µs per 64-byte block, which is too slow for native-lean verifiers that hash
megabytes (docs/zk-formal/DESIGN.md §7, R8).

This module defines `sha256Fast`, the same function written for the compiler
(`UInt32` words, the 64 rounds as one tail-recursive loop whose state and
16-word schedule window are unboxed arguments, no per-round allocation), and
proves in the kernel

  `sha256_eq_sha256Fast : @sha256 = @sha256Fast`.

The theorem is tagged `@[csimp]`, so the *compiler* replaces every call of
`sha256` by `sha256Fast`.  The kernel, and therefore every statement and
proof, still sees only `sha256`: the trusted specification is unchanged and
this module adds no axiom (the equality is an ordinary kernel-checked
theorem).  `sha256Fast` is `@[noinline]` so that inlining cannot undo the
redirect at call sites.

Proof structure (each fast layer mirrors one spec layer):
* word operations: `UInt32` op `.toNat` = the spec's `Nat` op (`add32`,
  `rotr`, `ch`, `maj`, `bsig0/1`, `ssig0/1`);
* `roundsF_spec`: the round loop = `SHA256.rounds` on the sliding window;
* `readWords_spec`, `compressF_spec`, `blocksF_spec`: block parsing and
  the block loop = `SHA256.words`/`compress`/`blocks`;
* `padF`: padding on bytes = `SHA256.pad` on their values.
-/

namespace ArenaCore
namespace SHA256Fast

open SHA256

/-! ## The fast implementation -/

/-- Eight working variables (or chaining words), unboxed. -/
structure St where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

@[inline] def rotrF (x n m : UInt32) : UInt32 := (x >>> n) ||| (x <<< m)
@[inline] def chF (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((x ^^^ 0xFFFFFFFF) &&& z)
@[inline] def majF (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
@[inline] def bsig0F (x : UInt32) : UInt32 := rotrF x 2 30 ^^^ rotrF x 13 19 ^^^ rotrF x 22 10
@[inline] def bsig1F (x : UInt32) : UInt32 := rotrF x 6 26 ^^^ rotrF x 11 21 ^^^ rotrF x 25 7
@[inline] def ssig0F (x : UInt32) : UInt32 := rotrF x 7 25 ^^^ rotrF x 18 14 ^^^ (x >>> 3)
@[inline] def ssig1F (x : UInt32) : UInt32 := rotrF x 17 15 ^^^ rotrF x 19 13 ^^^ (x >>> 10)

/-- Round constants as `UInt32`. -/
def KF : List UInt32 :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The rounds, one per constant in `ks`; `w0..w15` is the schedule window
(`w0` = the current word).  Tail-recursive: compiles to a loop. -/
def roundsF : List UInt32 → (a b c d e f g h : UInt32) →
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) → St
  | [], a, b, c, d, e, f, g, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨a, b, c, d, e, f, g, h⟩
  | k :: ks, a, b, c, d, e, f, g, h,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 =>
    let t1 := h + bsig1F e + chF e f g + k + w0
    let t2 := bsig0F a + majF a b c
    roundsF ks (t1 + t2) a b c (d + t1) e f g
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      ((ssig1F w14 + w9) + (ssig0F w1 + w0))

/-- Big-endian word from four bytes. -/
@[inline] def be32 (a b c d : UInt8) : UInt32 :=
  a.toUInt32 * 16777216 + b.toUInt32 * 65536 + c.toUInt32 * 256 + d.toUInt32

/-- Read `n` big-endian words; returns the words and the rest. -/
def readWords : Nat → List UInt8 → List UInt32 × List UInt8
  | 0, l => ([], l)
  | n + 1, a :: b :: c :: d :: rest =>
    let r := readWords n rest
    (be32 a b c d :: r.1, r.2)
  | _ + 1, l => ([], l)

/-- One compression (16 words). -/
def compressF (s : St) (ws : List UInt32) : St :=
  match ws with
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] =>
    let r := roundsF KF s.a s.b s.c s.d s.e s.f s.g s.h
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩
  | _ => s

/-- The block loop (at most `n` blocks). -/
def blocksF : Nat → St → List UInt8 → St
  | 0, s, _ => s
  | n + 1, s, l =>
    match l with
    | [] => s
    | _ :: _ =>
      let r := readWords 16 l
      blocksF n (compressF s r.1) r.2

/-- Padding on bytes. -/
def padF (m : List UInt8) : List UInt8 :=
  let len := m.length
  m ++ [0x80] ++ List.replicate ((119 - len % 64) % 64) 0 ++ Bytes.beN 8 (8 * len)

def H0F : St := ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- Chaining words as the spec's `Nat` list. -/
def St.toList (s : St) : List Nat :=
  [s.a.toNat, s.b.toNat, s.c.toNat, s.d.toNat, s.e.toNat, s.f.toNat, s.g.toNat, s.h.toNat]

/-- Working variables as the spec's `Vars`. -/
def St.toVars (s : St) : Vars :=
  ⟨s.a.toNat, s.b.toNat, s.c.toNat, s.d.toNat, s.e.toNat, s.f.toNat, s.g.toNat, s.h.toNat⟩

end SHA256Fast

open SHA256Fast in
/-- Fast compiled SHA-256 (equal to `sha256`: `sha256_eq_sha256Fast`). -/
@[noinline] def sha256Fast (m : Bytes) : Digest :=
  let p := padF m
  SHA256.digestBytes (blocksF (p.length / 64) H0F p).toList

/-! ## Proof of equality with the specification -/

namespace SHA256Fast

open SHA256

theorem add_toNat (a b : UInt32) : (a + b).toNat = add32 a.toNat b.toNat := by
  simp [add32, UInt32.toNat_add]

theorem rotrF_toNat (x n m : UInt32) (hn0 : 0 < n.toNat) (hn : n.toNat < 32)
    (hm : m.toNat = 32 - n.toNat) :
    (rotrF x n m).toNat = rotr x.toNat n.toNat := by
  have hx := x.toNat_lt
  have hm32 : m.toNat % 32 = m.toNat := Nat.mod_eq_of_lt (by omega)
  have hn32 : n.toNat % 32 = n.toNat := Nat.mod_eq_of_lt hn
  simp only [rotrF, rotr, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight]
  rw [hm32, hn32, hm]
  have hmask : mask32 = 2 ^ 32 - 1 := rfl
  rw [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.or_mod_two_pow]
  have : x.toNat >>> n.toNat < 2 ^ 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  rw [Nat.mod_eq_of_lt this]

theorem chF_toNat (x y z : UInt32) : (chF x y z).toNat = ch x.toNat y.toNat z.toNat := by
  simp only [chF, ch, UInt32.toNat_and, UInt32.toNat_xor]; rfl

theorem majF_toNat (x y z : UInt32) : (majF x y z).toNat = maj x.toNat y.toNat z.toNat := by
  simp only [majF, maj, UInt32.toNat_and, UInt32.toNat_xor]

theorem bsig0F_toNat (x : UInt32) : (bsig0F x).toNat = bsig0 x.toNat := by
  simp only [bsig0F, bsig0, UInt32.toNat_xor]
  rw [rotrF_toNat _ _ _ (by decide) (by decide) (by decide), rotrF_toNat _ _ _ (by decide) (by decide) (by decide),
    rotrF_toNat _ _ _ (by decide) (by decide) (by decide)]; rfl

theorem bsig1F_toNat (x : UInt32) : (bsig1F x).toNat = bsig1 x.toNat := by
  simp only [bsig1F, bsig1, UInt32.toNat_xor]
  rw [rotrF_toNat _ _ _ (by decide) (by decide) (by decide), rotrF_toNat _ _ _ (by decide) (by decide) (by decide),
    rotrF_toNat _ _ _ (by decide) (by decide) (by decide)]; rfl

theorem ssig0F_toNat (x : UInt32) : (ssig0F x).toNat = ssig0 x.toNat := by
  simp only [ssig0F, ssig0, UInt32.toNat_xor, UInt32.toNat_shiftRight]
  rw [rotrF_toNat _ _ _ (by decide) (by decide) (by decide), rotrF_toNat _ _ _ (by decide) (by decide) (by decide)]; rfl

theorem ssig1F_toNat (x : UInt32) : (ssig1F x).toNat = ssig1 x.toNat := by
  simp only [ssig1F, ssig1, UInt32.toNat_xor, UInt32.toNat_shiftRight]
  rw [rotrF_toNat _ _ _ (by decide) (by decide) (by decide), rotrF_toNat _ _ _ (by decide) (by decide) (by decide)]; rfl

theorem roundsF_spec (ks : List UInt32) (a b c d e f g h : UInt32)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32) :
    (roundsF ks a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15).toVars =
      rounds ⟨a.toNat, b.toNat, c.toNat, d.toNat, e.toNat, f.toNat, g.toNat, h.toNat⟩
        (ks.map UInt32.toNat)
        [w0.toNat, w1.toNat, w2.toNat, w3.toNat, w4.toNat, w5.toNat, w6.toNat, w7.toNat,
         w8.toNat, w9.toNat, w10.toNat, w11.toNat, w12.toNat, w13.toNat, w14.toNat, w15.toNat] := by
  induction ks generalizing a b c d e f g h
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 with
  | nil => rfl
  | cons k ks ih =>
    simp only [roundsF, List.map_cons, rounds]
    rw [ih]
    simp only [add_toNat, bsig0F_toNat, bsig1F_toNat, chF_toNat, majF_toNat, ssig0F_toNat,
      ssig1F_toNat]
    rfl

theorem KF_map : KF.map UInt32.toNat = K := by decide

theorem be32_toNat (a b c d : UInt8) :
    (be32 a b c d).toNat = ((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  simp only [be32, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32]
  have e1 : (16777216 : UInt32).toNat = 16777216 := rfl
  have e2 : (65536 : UInt32).toNat = 65536 := rfl
  have e3 : (256 : UInt32).toNat = 256 := rfl
  rw [e1, e2, e3]
  omega

theorem readWords_spec : ∀ (n : Nat) (l : List UInt8), 4 * n ≤ l.length →
    (readWords n l).1.map UInt32.toNat = words ((l.take (4 * n)).map UInt8.toNat) ∧
    (readWords n l).1.length = n ∧
    (readWords n l).2 = l.drop (4 * n)
  | 0, l, _ => by simp [readWords, words]
  | n + 1, a :: b :: c :: d :: rest, hl => by
    have hl' : 4 * n ≤ rest.length := by simp at hl; omega
    obtain ⟨h1, h2, h3⟩ := readWords_spec n rest hl'
    have et : 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [readWords, List.map_cons, et, List.take_succ_cons, words, be32_toNat, h1]
    · simp only [readWords, List.length_cons, h2]
    · simp only [readWords, h3, et, List.drop_succ_cons]
  | n + 1, [], hl => by simp at hl
  | n + 1, [_], hl => by simp at hl; omega
  | n + 1, [_, _], hl => by simp at hl; omega
  | n + 1, [_, _, _], hl => by simp at hl; omega

theorem compressF_spec (s : St) (ws : List UInt32) (blk : List Nat) (hlen : ws.length = 16)
    (hw : ws.map UInt32.toNat = words blk) :
    (compressF s ws).toList = compress s.toList blk := by
  match ws, hlen with
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15], _ =>
    simp only [compress, ← hw, List.map_cons, List.map_nil]
    have hv : ofList s.toList =
        ⟨s.a.toNat, s.b.toNat, s.c.toNat, s.d.toNat, s.e.toNat, s.f.toNat, s.g.toNat, s.h.toNat⟩ :=
      rfl
    rw [hv, ← KF_map, ← roundsF_spec]
    simp only [compressF, St.toList, St.toVars, add_toNat]
    rfl

theorem blocksF_spec : ∀ (n : Nat) (s : St) (l : List UInt8), l.length % 64 = 0 →
    (blocksF n s l).toList = blocks n s.toList (l.map UInt8.toNat)
  | 0, s, l, _ => by simp [blocksF, blocks]
  | n + 1, s, [], _ => by simp [blocksF, blocks]
  | n + 1, s, x :: xs, hl => by
    have h64 : 4 * 16 ≤ (x :: xs).length := by
      have : 0 < (x :: xs).length := by simp
      omega
    obtain ⟨h1, h2, h3⟩ := readWords_spec 16 (x :: xs) h64
    simp only [blocksF, List.map_cons, blocks]
    rw [blocksF_spec n _ _ (by rw [h3, List.length_drop]; omega), h3,
      compressF_spec _ _ _ h2 h1, List.map_drop, List.map_take]
    rfl

theorem padF_spec (m : List UInt8) : pad (m.map UInt8.toNat) = (padF m).map UInt8.toNat := by
  simp only [pad, padF, List.length_map, List.map_append, List.map_cons, List.map_nil,
    List.map_replicate]
  rfl

theorem padF_length (m : List UInt8) : (padF m).length % 64 = 0 := by
  simp only [padF, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    Bytes.beN_length]
  omega

end SHA256Fast

open SHA256Fast in
/-- **The fast SHA-256 is the specification.**  Kernel-checked; `@[csimp]`
makes compiled code call `sha256Fast` wherever `sha256` is used. -/
@[csimp] theorem sha256_eq_sha256Fast : @sha256 = @sha256Fast := by
  funext m
  simp only [sha256, sha256Fast]
  have h0 : SHA256.H0 = H0F.toList := rfl
  rw [padF_spec, List.length_map, h0, ← blocksF_spec _ _ _ (padF_length m)]

end ArenaCore
