import NearSpecV3.Wasm.Crypto

/-!
# ML-DSA-65 signature verification (FIPS 204, final), as nearcore performs it

nearcore 2.13.4 verifies an ML-DSA-65 signature in `Signature::verify`
(`core/crypto/src/signature.rs:1125-1128`): `UnparsedPublicKey::new(&ML_DSA_65, pk).verify(data, sig)`
with `aws-lc-rs` 1.16.2 (`Cargo.toml:156`, feature `unstable`). That is `EVP_DigestVerify` with no
digest (`aws-lc-rs/src/pqdsa/signature.rs:104-113`), i.e. `pkey_pqdsa_verify_generic` in RAW mode
(`aws-lc/crypto/fipsmodule/evp/p_pqdsa.c:183-189`), which calls `ml_dsa_65_verify` with an **empty
context string** (`NULL, 0`). So nearcore uses **pure ML-DSA, ctx = ""**:
`M' = 0x00 ‖ 0x00 ‖ M` (`mld_prepare_domain_separation_prefix`, `MLD_PREHASH_NONE`), and then
`mld_sign_verify_internal` (`aws-lc/crypto/fipsmodule/ml_dsa/mldsa/sign.c:976-1102`), the
FIPS 204 Algorithm 8 `ML-DSA.Verify_internal`. The signed message `M` is the 32-byte transaction
hash (`transaction.rs:291-293`) or the 32-byte NEP-461 delegate hash (`action/delegate.rs:89, 213`).

Parameters (FIPS 204 Table 1, ML-DSA-65): `q = 8380417`, `d = 13`, `τ = 49`, `λ = 192`
(`c̃` is 48 bytes), `γ1 = 2^19`, `γ2 = (q−1)/32`, `(k, ℓ) = (6, 5)`, `η = 4`, `β = 196`, `ω = 55`;
public key 1,952 bytes, signature 3,309 bytes (`signature.rs:21-25`).

Rejections, each matching the library:

* signature length ≠ 3,309 (`sign.c:1022-1026`; nearcore's Borsh reads exactly 3,309 bytes);
* malformed hint encoding (`packing.c:192-268`, FIPS 204 Algorithm 21): a per-polynomial running
  count that decreases or exceeds `ω`; indices not strictly increasing inside one polynomial; a
  non-zero byte in the unused index slots;
* `‖z‖∞ ≥ γ1 − β` (`sign.c:1036-1040`);
* `c̃ ≠ H(μ ‖ w1Encode(UseHint(h, w'_approx)))`.

The public key has no invalid encoding: `pkDecode` is total (10-bit `t1` coefficients), and
`parse_pqdsa_public_key` checks only the length, which the Borsh type fixes at 1,952.

Arithmetic is on `UInt64` residues in `[0, q)`; products are `< 2^46`. Rejection sampling
(`RejNTTPoly`, `SampleInBall`) squeezes the XOF block by block with a fuel bound far beyond any
realistic need (`Fuel.blocks`); exhausting it returns `false`. The probability of reaching it is
below `2^-1000` for every input, so this is not a reachable divergence from the library.

Pinned by `NearSpecV3/Examples/MlDsaVectors.lean`: NIST ACVP `ML-DSA-sigVer-FIPS204` vectors
(groups 3, 9, 10: pure external with contexts, external-μ, internal) and the pinned crate's own
verdicts on nearcore-shaped (32-byte message, empty context) valid, mutated and malformed
signatures, generated through `near_crypto::Signature::verify` itself.
-/

namespace NearSpecV3.MlDsa65

open NearSpecV3.Wasm.Crypto (keccakF)

/-! ## Parameters -/

def q : UInt64 := 8380417
def qN : Nat := 8380417
def dBits : Nat := 13
def tau : Nat := 49
def ctildeBytes : Nat := 48
def gamma1 : Nat := 524288
def gamma2 : Nat := 261888
def kDim : Nat := 6
def lDim : Nat := 5
def beta : Nat := 196
def omega : Nat := 55
def pkBytes : Nat := 1952
def sigBytes : Nat := 3309
/-- `z` packing: 20 bits per coefficient, 640 bytes per polynomial. -/
def zPolyBytes : Nat := 640
/-- `t1` packing: 10 bits per coefficient, 320 bytes per polynomial. -/
def t1PolyBytes : Nat := 320

/-! ## SHAKE128 / SHAKE256 (FIPS 202 §6.2), squeezing on demand -/

/-- Absorb `m` into a fresh Keccak state with rate `rate` bytes and the SHAKE pad `0x1F … 0x80`;
returns the state ready for the first squeeze. -/
def absorb (rate : Nat) (m : ByteArray) : Array UInt64 := Id.run do
  let padLen := rate - m.size % rate
  let mut p := m
  for i in [0:padLen] do
    let v : UInt8 := (if i = 0 then 0x1F else 0) ||| (if i = padLen - 1 then 0x80 else 0)
    p := p.push v
  let mut st := Array.replicate 25 (0 : UInt64)
  for blk in [0:p.size / rate] do
    for w in [0:rate / 8] do
      let mut lane : UInt64 := 0
      for k in [0:8] do
        lane := lane ||| ((p.get! (blk * rate + 8 * w + k)).toUInt64 <<< (8 * k).toUInt64)
      st := st.set! w (st[w]! ^^^ lane)
    st := keccakF st
  st

/-- The first `rate` output bytes of a state (one squeeze block). -/
def block (rate : Nat) (st : Array UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:rate] do
    out := out.push ((st[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8)
  out

/-- `outLen` bytes of SHAKE output with rate `rate` (168: SHAKE128, 136: SHAKE256). -/
def shake (rate : Nat) (m : ByteArray) (outLen : Nat) : ByteArray := Id.run do
  let mut st := absorb rate m
  let mut out := ByteArray.empty
  for _ in [0:(outLen + rate - 1) / rate] do
    out := out ++ block rate st
    st := keccakF st
  out.extract 0 outLen

def shake128 (m : ByteArray) (n : Nat) : ByteArray := shake 168 m n
def shake256 (m : ByteArray) (n : Nat) : ByteArray := shake 136 m n

namespace Fuel
/-- Bound on squeeze blocks per rejection-sampled polynomial (and, times 136, on `SampleInBall`
byte draws). `RejNTTPoly` accepts a 3-byte candidate with probability `q / 2^23 > 0.999` and a
SHAKE128 block holds 56 candidates, so it needs 5 blocks almost always; running out of 4,096
blocks (229,376 candidates for 256 acceptances) has probability far below `2^-1000`.
`SampleInBall` accepts a byte for position `i ≥ 207` with probability `> 0.8`. -/
def blocks : Nat := 4096
end Fuel

/-! ## Arithmetic mod q -/

@[inline] def addq (a b : UInt64) : UInt64 := (a + b) % q
@[inline] def subq (a b : UInt64) : UInt64 := (a + q - b) % q
@[inline] def mulq (a b : UInt64) : UInt64 := (a * b) % q

def powq (b : UInt64) (e : Nat) : UInt64 := Id.run do
  let mut r : UInt64 := 1
  let mut x := b
  let mut e := e
  for _ in [0:64] do
    if e % 2 = 1 then r := mulq r x
    x := mulq x x
    e := e / 2
  r

/-- `BitRev8`. -/
def brv8 (m : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:8] do
    if (m >>> i) % 2 = 1 then r := r ||| (1 <<< (7 - i))
  r

/-- `zetas[m] = ζ^{BitRev8(m)} mod q`, `ζ = 1753` (FIPS 204 Appendix B). -/
def zetas : Array UInt64 := Array.ofFn (n := 256) fun m => powq 1753 (brv8 m.val)

/-- `NTT` (FIPS 204 Algorithm 41). -/
def ntt (w0 : Array UInt64) : Array UInt64 := Id.run do
  let mut w := w0
  let mut m := 0
  let mut len := 128
  for _ in [0:8] do
    let mut start := 0
    for _ in [0:256 / (2 * len)] do
      m := m + 1
      let z := zetas[m]!
      for j in [start:start + len] do
        let t := mulq z w[j + len]!
        let a := w[j]!
        w := w.set! (j + len) (subq a t)
        w := w.set! j (addq a t)
      start := start + 2 * len
    len := len / 2
  w

/-- `NTT⁻¹` (FIPS 204 Algorithm 42). -/
def invNtt (w0 : Array UInt64) : Array UInt64 := Id.run do
  let mut w := w0
  let mut m := 256
  let mut len := 1
  for _ in [0:8] do
    let mut start := 0
    for _ in [0:256 / (2 * len)] do
      m := m - 1
      let z := subq 0 zetas[m]!
      for j in [start:start + len] do
        let t := w[j]!
        let u := w[j + len]!
        w := w.set! j (addq t u)
        w := w.set! (j + len) (mulq z (subq t u))
      start := start + 2 * len
    len := 2 * len
  w.map (mulq 8347681)

def pointwise (a b : Array UInt64) : Array UInt64 := Array.ofFn (n := 256) fun i => mulq a[i.val]! b[i.val]!
def polyAdd (a b : Array UInt64) : Array UInt64 := Array.ofFn (n := 256) fun i => addq a[i.val]! b[i.val]!
def polySub (a b : Array UInt64) : Array UInt64 := Array.ofFn (n := 256) fun i => subq a[i.val]! b[i.val]!

/-! ## Sampling (FIPS 204 Algorithms 29, 30, 32) -/

/-- `RejNTTPoly(ρ ‖ s ‖ r)` (Algorithm 30) via `CoeffFromThreeBytes` (Algorithm 14). `none` only if
the fuel bound is exhausted. -/
def rejNttPoly (seed : ByteArray) : Option (Array UInt64) := Id.run do
  let mut st := absorb 168 seed
  let mut a : Array UInt64 := Array.mkEmpty 256
  for _ in [0:Fuel.blocks] do
    if a.size ≥ 256 then break
    let b := block 168 st
    st := keccakF st
    for i in [0:56] do
      if a.size < 256 then
        let b0 := (b.get! (3 * i)).toUInt64
        let b1 := (b.get! (3 * i + 1)).toUInt64
        let b2 := ((b.get! (3 * i + 2)) &&& 0x7F).toUInt64
        let z := (b2 <<< 16) ||| (b1 <<< 8) ||| b0
        if z < q then a := a.push z
  if a.size ≥ 256 then some a else none

/-- `ExpandA(ρ)` (Algorithm 32): `Â[r][s] = RejNTTPoly(ρ ‖ s ‖ r)`, row-major `k × ℓ`. -/
def expandA (rho : ByteArray) : Option (Array (Array UInt64)) := Id.run do
  let mut out : Array (Array UInt64) := Array.mkEmpty (kDim * lDim)
  for r in [0:kDim] do
    for s in [0:lDim] do
      match rejNttPoly ((rho.push s.toUInt8).push r.toUInt8) with
      | none => return none
      | some p => out := out.push p
  some out

/-- `SampleInBall(c̃)` (Algorithm 29), seeded with the full 48-byte `c̃` (FIPS 204 final; the
draft used only 32 bytes). Coefficients in `{0, 1, q−1}`. -/
def sampleInBall (ct : ByteArray) : Option (Array UInt64) := Id.run do
  let mut st := absorb 136 ct
  let mut buf := block 136 st
  st := keccakF st
  let mut signs : UInt64 := 0
  for i in [0:8] do
    signs := signs ||| ((buf.get! i).toUInt64 <<< (8 * i).toUInt64)
  let mut pos := 8
  let mut c := Array.replicate 256 (0 : UInt64)
  let mut i := 256 - tau
  for _ in [0:Fuel.blocks * 136] do
    if i ≥ 256 then break
    if pos ≥ buf.size then
      buf := block 136 st
      st := keccakF st
      pos := 0
    let j := (buf.get! pos).toNat
    pos := pos + 1
    if j ≤ i then
      c := c.set! i c[j]!
      let bit := (signs >>> (i + tau - 256).toUInt64) &&& 1
      c := c.set! j (if bit = 1 then q - 1 else 1)
      i := i + 1
  if i ≥ 256 then some c else none

/-! ## Encodings (FIPS 204 §7.1, Algorithms 16-28) -/

/-- Little-endian bit field of width `w` at bit offset `off` of `b` (`BitsToBytes` order). -/
@[inline] def bitsAt (b : ByteArray) (off w : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  let byte0 := off / 8
  let sh := off % 8
  -- at most 4 bytes cover a field of ≤ 20 bits plus a 7-bit shift
  for k in [0:4] do
    if byte0 + k < b.size then
      v := v ||| ((b.get! (byte0 + k)).toUInt64 <<< (8 * k).toUInt64)
  (v >>> sh.toUInt64) &&& ((1 <<< w.toUInt64) - 1)

/-- `pkDecode` (Algorithm 23): `ρ` and the six `t1` polynomials (10-bit `SimpleBitUnpack`). -/
def pkDecode (pk : ByteArray) : ByteArray × Array (Array UInt64) :=
  let rho := pk.extract 0 32
  let t1 := Array.ofFn (n := kDim) fun i =>
    let base := 8 * (32 + t1PolyBytes * i.val)
    Array.ofFn (n := 256) fun j => bitsAt pk (base + 10 * j.val) 10
  (rho, t1)

/-- `HintBitUnpack` (Algorithm 21), exactly `mld_unpack_hints` (`packing.c:192-268`). `none` on
a malformed encoding. `y` is the `ω + k = 61` byte tail of the signature. -/
def hintUnpack (y : ByteArray) : Option (Array (Array UInt64)) := Id.run do
  let mut h : Array (Array UInt64) := Array.replicate kDim (Array.replicate 256 0)
  let mut index := 0
  for i in [0:kDim] do
    let cnt := (y.get! (omega + i)).toNat
    if cnt < index || cnt > omega then return none
    let first := index
    for j in [first:cnt] do
      if j > first then
        if (y.get! (j - 1)).toNat ≥ (y.get! j).toNat then return none
      let pos := (y.get! j).toNat
      h := h.modify i (fun p => p.set! pos 1)
    index := cnt
  for j in [index:omega] do
    if y.get! j != 0 then return none
  some h

/-- `sigDecode` (Algorithm 27): `c̃`, `z` (centered integers, from `BitUnpack(·, γ1−1, γ1)`, 20
bits: `z = γ1 − v`), and the hint. `none` on a malformed hint. -/
def sigDecode (sig : ByteArray) : Option (ByteArray × Array (Array Int) × Array (Array UInt64)) :=
  let ct := sig.extract 0 ctildeBytes
  let z := Array.ofFn (n := lDim) fun i =>
    let base := 8 * (ctildeBytes + zPolyBytes * i.val)
    Array.ofFn (n := 256) fun j => (gamma1 : Int) - ((bitsAt sig (base + 20 * j.val) 20).toNat : Int)
  match hintUnpack (sig.extract (ctildeBytes + lDim * zPolyBytes) sigBytes) with
  | none => none
  | some h => some (ct, z, h)

/-- `‖z‖∞ < γ1 − β`. -/
def zNormOk (z : Array (Array Int)) : Bool :=
  z.all fun p => p.all fun c => c.natAbs < gamma1 - beta

def intToZq (c : Int) : UInt64 := (c % (qN : Int)).toNat.toUInt64

/-- `Decompose` (Algorithm 36) high part and `UseHint` (Algorithm 40), `m = 16`. -/
def useHint (hbit : UInt64) (r : UInt64) : UInt64 :=
  let rp := r.toNat
  let alpha := 2 * gamma2
  -- r0 = r+ mod± α, in (−α/2, α/2]
  let r0m := rp % alpha
  let r0 : Int := if r0m > alpha / 2 then (r0m : Int) - alpha else r0m
  let (r1, r0) : Nat × Int :=
    if (rp : Int) - r0 = (qN - 1 : Nat) then (0, r0 - 1)
    else (((rp : Int) - r0).toNat / alpha, r0)
  if hbit = 1 then
    if r0 > 0 then ((r1 + 1) % 16).toUInt64 else ((r1 + 15) % 16).toUInt64
  else r1.toUInt64

/-- `w1Encode` (Algorithm 28): 4 bits per coefficient, 128 bytes per polynomial. -/
def w1Encode (w1 : Array (Array UInt64)) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for p in w1 do
    for i in [0:128] do
      out := out.push (p[2 * i]! ||| (p[2 * i + 1]! <<< 4)).toUInt8
  out

/-! ## Verification (FIPS 204 Algorithms 7, 8) -/

/-- `ML-DSA.Verify_internal` given `μ` directly (the `externalMu` interface). -/
def verifyMu (pk : ByteArray) (mu : ByteArray) (sig : ByteArray) : Bool :=
  if pk.size != pkBytes || sig.size != sigBytes || mu.size != 64 then false else
  match sigDecode sig with
  | none => false
  | some (ct, z, h) =>
    if !zNormOk z then false else
    let (rho, t1) := pkDecode pk
    match expandA rho, sampleInBall ct with
    | some a, some c =>
      let cHat := ntt c
      let zHat := z.map fun p => ntt (p.map intToZq)
      let w1 := Array.ofFn (n := kDim) fun r =>
        let az := (List.range lDim).foldl
          (fun acc s => polyAdd acc (pointwise a[lDim * r.val + s]! zHat[s]!))
          (Array.replicate 256 0)
        let t1Hat := ntt (t1[r.val]!.map fun x => mulq x 8192)
        let wApprox := invNtt (polySub az (pointwise cHat t1Hat))
        Array.ofFn (n := 256) fun j => useHint h[r.val]![j.val]! wApprox[j.val]!
      let ct2 := shake256 (mu ++ w1Encode w1) ctildeBytes
      ct2 == ct
    | _, _ => false

/-- `ML-DSA.Verify_internal(pk, M', σ)` (Algorithm 8): `tr = H(pk, 64)`, `μ = H(tr ‖ M', 64)`. -/
def verifyInternal (pk : ByteArray) (m' : ByteArray) (sig : ByteArray) : Bool :=
  if pk.size != pkBytes then false else
  let tr := shake256 pk 64
  verifyMu pk (shake256 (tr ++ m') 64) sig

/-- Pure `ML-DSA.Verify(pk, M, σ, ctx)` (Algorithm 3): `M' = 0 ‖ |ctx| ‖ ctx ‖ M`. -/
def verifyCtx (pk : ByteArray) (msg : ByteArray) (sig : ByteArray) (ctx : ByteArray) : Bool :=
  if ctx.size > 255 then false
  else verifyInternal pk (((ByteArray.empty.push 0).push ctx.size.toUInt8) ++ ctx ++ msg) sig

/-- nearcore's `Signature::verify` arm for `(MLDSA65, MLDSA65)`: pure ML-DSA-65, empty context,
on the byte lists the Lean codecs carry. -/
def verify (pk : List UInt8) (sig : List UInt8) (msg : List UInt8) : Bool :=
  verifyCtx ⟨pk.toArray⟩ ⟨msg.toArray⟩ ⟨sig.toArray⟩ ByteArray.empty

end NearSpecV3.MlDsa65
