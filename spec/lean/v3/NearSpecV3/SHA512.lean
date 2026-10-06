import ArenaCore.Bytes

/-!
# SHA-512 (FIPS 180-4)

Leaf module of `near/pv86/chunk-validation/v0` (domain D1): the hash inside Ed25519
signature verification (`k = SHA-512(R ‖ A ‖ M) mod ℓ`, RFC 8032 §5.1.7; ed25519-dalek
2.2.0 `src/verifying.rs:521-559` with `CtxDigest = sha2::Sha512`, `:563-565`).

A direct transcription of FIPS 180-4 §4.1.3 (functions), §4.2.3 (constants),
§5.1.2 (padding), §5.3.5 (initial hash value) and §6.4 (hash computation), in the
style of `ArenaCore.SHA256`: 64-bit words are `Nat` values `< 2^64`, every word
operation is an explicit `Nat` bit operation followed by `% 2^64` (the Lean kernel
has GMP-accelerated `Nat.add/mul/mod/land/lor/xor/shiftLeft/shiftRight`), and only
structural recursion is used, so `decide +kernel` evaluates it on concrete inputs.

The function is total on all byte strings; the 128-bit length field is `8·len mod 2^128`
(exactly as `beN 16` encodes it), which only matters for inputs far beyond any limit.

**Status.** Tested (not proved) equal to Python `hashlib.sha512` on
`oracle/fixtures/v3/ed25519/sha512.jsonl` (all lengths 0..300 and random lengths up to
1000) by `nearspec-v3-test-ed25519`; kernel-checked on the FIPS "abc" and "" digests in
`NearSpecV3/Examples/Ed25519Kernel.lean`. Proved: `sha512_length` (digest is 64 bytes).
-/

namespace NearSpecV3
namespace SHA512

open ArenaCore

/-- 2^64 - 1 -/
def mask64 : Nat := 0xFFFFFFFFFFFFFFFF

/-- Addition modulo 2^64. -/
def add64 (a b : Nat) : Nat := (a + b) % 18446744073709551616

/-- Right rotation of a 64-bit word (`x < 2^64`, `0 < n < 64`), FIPS 180-4 §3.2. -/
def rotr (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (64 - n))) &&& mask64

/-- §4.1.3 (4.8), (4.9). -/
def ch (x y z : Nat) : Nat := (x &&& y) ^^^ ((x ^^^ mask64) &&& z)
def maj (x y z : Nat) : Nat := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
/-- §4.1.3 (4.10)–(4.13). -/
def bsig0 (x : Nat) : Nat := rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39
def bsig1 (x : Nat) : Nat := rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41
def ssig0 (x : Nat) : Nat := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)
def ssig1 (x : Nat) : Nat := rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)

/-- Round constants K₀..K₇₉ (FIPS 180-4 §4.2.3). -/
def K : List Nat :=
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- Initial hash value H⁽⁰⁾ (FIPS 180-4 §5.3.5). -/
def H0 : List Nat :=
  [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- Big-endian 64-bit words from a list of byte values (length multiple of 8). -/
def words : List Nat → List Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    (((((((b0 * 256 + b1) * 256 + b2) * 256 + b3) * 256 + b4) * 256 + b5) * 256 + b6) * 256
      + b7) :: words rest
  | _ => []

/-- Next message-schedule window (§6.4.2 step 1). The window holds Wₜ..Wₜ₊₁₅; the
result holds Wₜ₊₁..Wₜ₊₁₆ where Wₜ₊₁₆ = σ₁(Wₜ₊₁₄) + Wₜ₊₉ + σ₀(Wₜ₊₁) + Wₜ. -/
def nextWindow : List Nat → List Nat
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] =>
    [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
     add64 (add64 (ssig1 w14) w9) (add64 (ssig0 w1) w0)]
  | ws => ws

/-- Working variables (a,b,c,d,e,f,g,h). -/
structure Vars where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

/-- One compression round with constant `k` and schedule word `w` (§6.4.2 step 3). -/
def round (v : Vars) (k w : Nat) : Vars :=
  let t1 := add64 (add64 (add64 (add64 v.h (bsig1 v.e)) (ch v.e v.f v.g)) k) w
  let t2 := add64 (bsig0 v.a) (maj v.a v.b v.c)
  { a := add64 t1 t2, b := v.a, c := v.b, d := v.c,
    e := add64 v.d t1, f := v.e, g := v.f, h := v.g }

/-- The 80 rounds; `win` is the current schedule window (head = Wₜ). -/
def rounds : Vars → List Nat → List Nat → Vars
  | v, k :: ks, win => rounds (round v k (win.headD 0)) ks (nextWindow win)
  | v, [], _ => v

def ofList (h : List Nat) : Vars :=
  { a := h.getD 0 0, b := h.getD 1 0, c := h.getD 2 0, d := h.getD 3 0,
    e := h.getD 4 0, f := h.getD 5 0, g := h.getD 6 0, h := h.getD 7 0 }

/-- Process one 128-byte block (given as 128 byte values), §6.4.2 steps 2–4. -/
def compress (h : List Nat) (block : List Nat) : List Nat :=
  let v := rounds (ofList h) K (words block)
  [add64 (h.getD 0 0) v.a, add64 (h.getD 1 0) v.b, add64 (h.getD 2 0) v.c,
   add64 (h.getD 3 0) v.d, add64 (h.getD 4 0) v.e, add64 (h.getD 5 0) v.f,
   add64 (h.getD 6 0) v.g, add64 (h.getD 7 0) v.h]

/-- Fold `compress` over consecutive 128-byte blocks; `n` bounds the number of blocks
(structural recursion). -/
def blocks : Nat → List Nat → List Nat → List Nat
  | 0, h, _ => h
  | n + 1, h, msg =>
    match msg with
    | [] => h
    | _ => blocks n (compress h (msg.take 128)) (msg.drop 128)

/-- Padding (§5.1.2): `m ‖ 0x80 ‖ 0^k ‖ be128(8·len)` with total length a multiple
of 128 bytes. -/
def pad (m : List Nat) : List Nat :=
  let len := m.length
  let k := (239 - len % 128) % 128
  m ++ [0x80] ++ List.replicate k 0 ++ (Bytes.beN 16 (8 * len)).map UInt8.toNat

/-- Big-endian bytes of the final hash words (§6.4.2, H⁽ᴺ⁾ = H₀ ‖ … ‖ H₇). -/
def digestBytes (h : List Nat) : Bytes :=
  h.flatMap fun x => Bytes.beN 8 x

theorem compress_length (h b : List Nat) : (compress h b).length = 8 := rfl

theorem blocks_length (n : Nat) (h msg : List Nat) (hh : h.length = 8) :
    (blocks n h msg).length = 8 := by
  induction n generalizing h msg with
  | zero => simpa [blocks] using hh
  | succ n ih =>
    cases msg with
    | nil => simpa [blocks] using hh
    | cons x xs => simp only [blocks]; exact ih _ _ (compress_length _ _)

theorem digestBytes_length (h : List Nat) (hh : h.length = 8) :
    (digestBytes h).length = 64 := by
  match h, hh with
  | [_, _, _, _, _, _, _, _], _ => simp [digestBytes, Bytes.beN_length]

theorem pad_length_mod (m : List Nat) : (pad m).length % 128 = 0 := by
  simp only [pad, List.length_append, List.length_replicate, List.length_map,
    Bytes.beN_length, List.length_singleton]
  omega

end SHA512

/-- SHA-512 of a byte string (FIPS 180-4 §6.4). -/
def sha512 (m : ArenaCore.Bytes) : ArenaCore.Bytes :=
  let p := SHA512.pad (m.map UInt8.toNat)
  SHA512.digestBytes (SHA512.blocks (p.length / 128) SHA512.H0 p)

/-- SHA-512 digests are always 64 bytes. -/
theorem sha512_length (m : ArenaCore.Bytes) : (sha512 m).length = 64 :=
  SHA512.digestBytes_length _ (SHA512.blocks_length _ _ _ rfl)

end NearSpecV3
