import NearSpec.SHA256
/-!
# Hash functions behind NEAR's D3α hash host functions

* `sha256`: the single SHA-256 of the trusted tree (`NearSpec.sha256` = `ArenaCore.sha256`), shared
  with L5/D0/D1.
* `keccak256`/`keccak512`: original Keccak (pad `0x01 … 0x80`, not SHA-3's `0x06`), as RustCrypto
  `sha3::Keccak256`/`Keccak512` used by nearcore (`wasmtime_runner/logic.rs` `keccak256`/`keccak512`).
  Keccak-f[1600] per FIPS 202 §3, with rate 1088/576 bits.
* `ripemd160`: RIPEMD-160 (Dobbertin, Bosselaers, Preneel 1996), as RustCrypto `ripemd::Ripemd160`.

All are total functions on byte arrays; loops are bounded by the input length.
-/
namespace NearSpecV3.Wasm.Crypto

def sha256 (m : ByteArray) : ByteArray := ⟨(NearSpec.sha256 m.toList).toArray⟩

/-! ## Keccak-f[1600] -/

def rc : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- rotation offsets r[x + 5y] -/
def rotc : Array UInt64 := #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

def rotl64 (v : UInt64) (n : UInt64) : UInt64 := if n = 0 then v else (v <<< n) ||| (v >>> (64 - n))

def keccakF (a0 : Array UInt64) : Array UInt64 := Id.run do
  let mut a := a0
  for r in [0:24] do
    -- θ
    let c := Array.ofFn (n := 5) fun x =>
      a[x.val]! ^^^ a[x.val + 5]! ^^^ a[x.val + 10]! ^^^ a[x.val + 15]! ^^^ a[x.val + 20]!
    for x in [0:5] do
      let d := c[(x + 4) % 5]! ^^^ rotl64 c[(x + 1) % 5]! 1
      for y in [0:5] do
        a := a.set! (x + 5 * y) (a[x + 5 * y]! ^^^ d)
    -- ρ and π: B[y, 2x+3y] = rot(A[x,y], r[x,y])
    let mut b := Array.replicate 25 (0 : UInt64)
    for x in [0:5] do
      for y in [0:5] do
        b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl64 a[x + 5 * y]! rotc[x + 5 * y]!)
    -- χ
    for x in [0:5] do
      for y in [0:5] do
        a := a.set! (x + 5 * y)
          (b[x + 5 * y]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!))
    -- ι
    a := a.set! 0 (a[0]! ^^^ rc[r]!)
  a

/-- Keccak sponge with rate `rate` bytes, original Keccak padding, `outLen` bytes of output
(`outLen ≤ rate`, true for 256/512). -/
def keccak (rate outLen : Nat) (m : ByteArray) : ByteArray := Id.run do
  -- pad: m ‖ 0x01 ‖ 0* ‖ 0x80 (the 0x01 and 0x80 merge into 0x81 when one byte is left)
  let padLen := rate - m.size % rate
  let mut p := m
  for i in [0:padLen] do
    let v : UInt8 := (if i = 0 then 0x01 else 0) ||| (if i = padLen - 1 then 0x80 else 0)
    p := p.push v
  let mut st := Array.replicate 25 (0 : UInt64)
  for blk in [0:p.size / rate] do
    for w in [0:rate / 8] do
      let mut lane : UInt64 := 0
      for k in [0:8] do
        lane := lane ||| ((p.get! (blk * rate + 8 * w + k)).toUInt64 <<< (8 * k).toUInt64)
      st := st.set! w (st[w]! ^^^ lane)
    st := keccakF st
  let mut out := ByteArray.empty
  for i in [0:outLen] do
    out := out.push ((st[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8)
  out

def keccak256 (m : ByteArray) : ByteArray := keccak 136 32 m
def keccak512 (m : ByteArray) : ByteArray := keccak 72 64 m

/-! ## RIPEMD-160 -/

def rl : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
def rr : Array Nat := #[5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]
def sl : Array UInt32 := #[11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
def sr : Array UInt32 := #[8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]
def kl : Array UInt32 := #[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
def kr : Array UInt32 := #[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

def rot32 (x n : UInt32) : UInt32 := if n = 0 then x else (x <<< n) ||| (x >>> (32 - n))

def rf (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((~~~ x) &&& z)
  else if j < 48 then (x ||| (~~~ y)) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& (~~~ z))
  else x ^^^ (y ||| (~~~ z))

def ripemd160 (m : ByteArray) : ByteArray := Id.run do
  let bitLen := 8 * m.size
  let mut p := m.push 0x80
  while p.size % 64 ≠ 56 do p := p.push 0
  for i in [0:8] do p := p.push (UInt8.ofNat ((bitLen / 256 ^ i) % 256))
  let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  for blk in [0:p.size / 64] do
    let x := Array.ofFn (n := 16) fun i =>
      (p.get! (blk * 64 + 4 * i.val)).toUInt32 ||| ((p.get! (blk * 64 + 4 * i.val + 1)).toUInt32 <<< 8) |||
      ((p.get! (blk * 64 + 4 * i.val + 2)).toUInt32 <<< 16) ||| ((p.get! (blk * 64 + 4 * i.val + 3)).toUInt32 <<< 24)
    let mut al := h[0]!; let mut bl := h[1]!; let mut cl := h[2]!; let mut dl := h[3]!; let mut el := h[4]!
    let mut ar := h[0]!; let mut br := h[1]!; let mut cr := h[2]!; let mut dr := h[3]!; let mut er := h[4]!
    for j in [0:80] do
      let t := rot32 (al + rf j bl cl dl + x[rl[j]!]! + kl[j / 16]!) sl[j]! + el
      al := el; el := dl; dl := rot32 cl 10; cl := bl; bl := t
      let t' := rot32 (ar + rf (79 - j) br cr dr + x[rr[j]!]! + kr[j / 16]!) sr[j]! + er
      ar := er; er := dr; dr := rot32 cr 10; cr := br; br := t'
    let t := h[1]! + cl + dr
    h := #[t, h[2]! + dl + er, h[3]! + el + ar, h[4]! + al + br, h[0]! + bl + cr]
  let mut out := ByteArray.empty
  for w in h do
    for k in [0:4] do out := out.push ((w >>> (8 * k).toUInt32).toUInt8)
  out

end NearSpecV3.Wasm.Crypto
