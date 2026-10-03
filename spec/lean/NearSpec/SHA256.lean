import NearSpec.Bytes

/-!
# SHA-256 (FIPS 180-4), kernel-reducible

nearcore's `CryptoHash::hash_bytes` is SHA-256 (`core/primitives-core/src/hash.rs`).

Words are `Nat`s kept `< 2^32`; all arithmetic uses `Nat` operations that the
Lean kernel evaluates with GMP acceleration (`+`, `%`, `/`, `&&&`, `|||`,
`^^^`, `<<<`, `>>>`). All recursion is structural, so `decide +kernel` can
evaluate hashes (no `native_decide`).

DUPLICATION NOTE: formal-core may define its own SHA-256. If it does, the two
must be proven equal (or this one replaced) before freeze; until then this is
the only SHA-256 the NEAR relation depends on.
-/

namespace NearSpec.SHA256

def M : Nat := 4294967296  -- 2^32

def rotr (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (32 - n))) % M

def ch (x y z : Nat) : Nat := (x &&& y) ^^^ ((M - 1 - x) &&& z)
def maj (x y z : Nat) : Nat := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : Nat) : Nat := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : Nat) : Nat := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def ssig0 (x : Nat) : Nat := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ssig1 (x : Nat) : Nat := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

def K : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

structure St where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

def H0 : St :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

def round (s : St) (k w : Nat) : St :=
  let t1 := (s.h + bsig1 s.e + ch s.e s.f s.g + k + w) % M
  let t2 := (bsig0 s.a + maj s.a s.b s.c) % M
  ⟨(t1 + t2) % M, s.a, s.b, s.c, (s.d + t1) % M, s.e, s.f, s.g⟩

/-- 64 rounds; `win` is the sliding 16-word message-schedule window. -/
def rounds : List Nat → List Nat → St → St
  | [], _, s => s
  | k :: ks, win, s =>
    let w0 := win.headD 0
    let nxt := (ssig1 (win.getD 14 0) + win.getD 9 0 + ssig0 (win.getD 1 0) + w0) % M
    rounds ks (win.tail ++ [nxt]) (round s k w0)

def compress (s : St) (block : List Nat) : St :=
  let r := rounds K block s
  ⟨(s.a + r.a) % M, (s.b + r.b) % M, (s.c + r.c) % M, (s.d + r.d) % M,
   (s.e + r.e) % M, (s.f + r.f) % M, (s.g + r.g) % M, (s.h + r.h) % M⟩

/-- Big-endian 32-bit words of a byte list (length divisible by 4 after padding). -/
def words : Bytes → List Nat
  | a :: b :: c :: d :: rest =>
    (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat) :: words rest
  | _ => []

/-- Process 16-word blocks; `fuel` = number of blocks. -/
def blocks : Nat → List Nat → St → St
  | 0, _, s => s
  | n + 1, ws, s => blocks n (ws.drop 16) (compress s (ws.take 16))

def pad (msg : Bytes) : Bytes :=
  let l := msg.length
  msg ++ [0x80] ++ zeros ((119 - l % 64) % 64) ++ be64 (8 * l)

def digestBytes (s : St) : Bytes :=
  be32 s.a ++ be32 s.b ++ be32 s.c ++ be32 s.d ++ be32 s.e ++ be32 s.f ++ be32 s.g ++ be32 s.h

def sha256 (msg : Bytes) : Bytes :=
  let p := pad msg
  digestBytes (blocks (p.length / 64) (words p) H0)

end NearSpec.SHA256

namespace NearSpec
/-- `CryptoHash::hash_bytes` in nearcore. -/
abbrev sha256 := SHA256.sha256
end NearSpec
