import ArenaCore.Bytes

/-!
# ArenaCore.SHA256

A direct specification implementation of SHA-256 (FIPS 180-4, §4.1.2,
§4.2.2, §5.1.1, §5.3.3, §6.2).  32-bit words are represented as `Nat`
values `< 2^32` and all word operations are explicit `Nat` bit operations
followed by `% 2^32`; the Lean kernel has GMP-accelerated implementations of
`Nat.add/mul/mod/land/lor/xor/shiftLeft/shiftRight`, which makes
`decide +kernel` on SHA-256 of small concrete messages practical.

Only structural recursion is used.  The function is total on all byte
strings (including lengths that would overflow the 64-bit length field in
FIPS 180-4; such inputs are beyond any arena limit and are hashed with the
length taken `mod 2^64`, exactly as `beN 8` encodes it).
-/

namespace ArenaCore
namespace SHA256

/-- 2^32 - 1 -/
def mask32 : Nat := 0xFFFFFFFF

/-- Addition modulo 2^32. -/
def add32 (a b : Nat) : Nat := (a + b) % 4294967296

/-- Right rotation of a 32-bit word (`x < 2^32`, `0 < n < 32`). -/
def rotr (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (32 - n))) &&& mask32

def ch (x y z : Nat) : Nat := (x &&& y) ^^^ ((x ^^^ mask32) &&& z)
def maj (x y z : Nat) : Nat := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : Nat) : Nat := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : Nat) : Nat := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def ssig0 (x : Nat) : Nat := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ssig1 (x : Nat) : Nat := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Round constants K₀..K₆₃ (FIPS 180-4 §4.2.2). -/
def K : List Nat :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Initial hash value H⁽⁰⁾ (FIPS 180-4 §5.3.3). -/
def H0 : List Nat :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Big-endian 32-bit words from a list of byte values (length multiple of 4). -/
def words : List Nat → List Nat
  | a :: b :: c :: d :: rest => (((a * 256 + b) * 256 + c) * 256 + d) :: words rest
  | _ => []

/-- Next message-schedule window (§6.2.2 step 1).  The window holds
Wₜ..Wₜ₊₁₅; the result holds Wₜ₊₁..Wₜ₊₁₆ where
Wₜ₊₁₆ = σ₁(Wₜ₊₁₄) + Wₜ₊₉ + σ₀(Wₜ₊₁) + Wₜ. -/
def nextWindow : List Nat → List Nat
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] =>
    [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
     add32 (add32 (ssig1 w14) w9) (add32 (ssig0 w1) w0)]
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

/-- One compression round with constant `k` and schedule word `w`. -/
def round (v : Vars) (k w : Nat) : Vars :=
  let t1 := add32 (add32 (add32 (add32 v.h (bsig1 v.e)) (ch v.e v.f v.g)) k) w
  let t2 := add32 (bsig0 v.a) (maj v.a v.b v.c)
  { a := add32 t1 t2, b := v.a, c := v.b, d := v.c,
    e := add32 v.d t1, f := v.e, g := v.f, h := v.g }

/-- The 64 rounds; `win` is the current schedule window (head = Wₜ). -/
def rounds : Vars → List Nat → List Nat → Vars
  | v, k :: ks, win => rounds (round v k (win.headD 0)) ks (nextWindow win)
  | v, [], _ => v

def ofList (h : List Nat) : Vars :=
  { a := h.getD 0 0, b := h.getD 1 0, c := h.getD 2 0, d := h.getD 3 0,
    e := h.getD 4 0, f := h.getD 5 0, g := h.getD 6 0, h := h.getD 7 0 }

/-- Process one 64-byte block (given as 64 byte values). -/
def compress (h : List Nat) (block : List Nat) : List Nat :=
  let v := rounds (ofList h) K (words block)
  [add32 (h.getD 0 0) v.a, add32 (h.getD 1 0) v.b, add32 (h.getD 2 0) v.c,
   add32 (h.getD 3 0) v.d, add32 (h.getD 4 0) v.e, add32 (h.getD 5 0) v.f,
   add32 (h.getD 6 0) v.g, add32 (h.getD 7 0) v.h]

/-- Fold `compress` over consecutive 64-byte blocks; `n` bounds the number of
blocks (structural recursion). -/
def blocks : Nat → List Nat → List Nat → List Nat
  | 0, h, _ => h
  | n + 1, h, msg =>
    match msg with
    | [] => h
    | _ => blocks n (compress h (msg.take 64)) (msg.drop 64)

/-- Padding (§5.1.1): `m ‖ 0x80 ‖ 0^k ‖ be64(8·len)` with total length a
multiple of 64. -/
def pad (m : List Nat) : List Nat :=
  let len := m.length
  let k := (119 - len % 64) % 64
  m ++ [0x80] ++ List.replicate k 0 ++ (Bytes.beN 8 (8 * len)).map UInt8.toNat

/-- Big-endian bytes of the final hash words. -/
def digestBytes (h : List Nat) : Bytes :=
  h.flatMap fun x => Bytes.beN 4 x

end SHA256

/-- SHA-256 of a byte string (FIPS 180-4). -/
def sha256 (m : Bytes) : Digest :=
  let p := SHA256.pad (m.map UInt8.toNat)
  SHA256.digestBytes (SHA256.blocks (p.length / 64) SHA256.H0 p)

namespace SHA256

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
    (digestBytes h).length = 32 := by
  match h, hh with
  | [_, _, _, _, _, _, _, _], _ => simp [digestBytes, Bytes.beN_length]

end SHA256

/-- SHA-256 digests are always 32 bytes. -/
theorem sha256_length (m : Bytes) : (sha256 m).length = 32 :=
  SHA256.digestBytes_length _ (SHA256.blocks_length _ _ _ rfl)

end ArenaCore
