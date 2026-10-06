import ZkFormal.NearV3.Sched.Tables.Scan
import ZkFormal.NearV3.Sched.Gen.Run

/-!
# ZkFormal.NearV3.Sched.Gen.Scan — honest trace of the bitmap scan `sscV3`

Instance τ with converted requests: the param row (`q₀..q₂ = base` bytes, `q₃, q₄, clo = D`
bytes), then per request `cid` 20 rows `ρ = 4y + u` with bits `b₀, b₁` at positions
`8y + 2u, 8y + 2u + 1`; byte register `q₀ = bm[y] >> 2u`, `qᵢ = bm[y+i]` (0 past the end);
`j` = set bits before the row, `cur` = value of the last set bit before (`base` first),
`cm` = value after `b₀`; remainders of `D·(pos+1)` mod 40 in 6 bits; `iy = (y − 4)⁻¹`,
`ikey = key⁻¹`. INC multiplicities: `us = bit ∧ (the increase is processed)`. Padding: zero.

Expected public traffic: `SPAR (τ, 1, n, base₀..₂, D₀..₂, 0, 0)` and
`SRAW (τ, cid_lo, cid_hi, s, r, bm₀..₄)` per converted request (none if no request).
-/

namespace ZkFormal.NearV3.Sched.Gen.Scan

open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Scan (act kP kS fQ tau nn base dd cid clo chi s r link q b0 b1 u0 u1 y iy
  e4 re Q0 Q1 rb0 rb1 cur cm j m key ikey zk0 us0 us1 width)

def byteOf (x i : Nat) : Nat := x / 256 ^ i % 256

def paramRow (R : Run) : Array Nat :=
  (zrow width).set! act 1 |>.set! kP 1 |>.set! tau R.tau |>.set! nn R.n |>.set! base R.base
    |>.set! dd R.D |>.set! (q 0) (byteOf R.base 0) |>.set! (q 1) (byteOf R.base 1)
    |>.set! (q 2) (byteOf R.base 2) |>.set! (q 3) (byteOf R.D 0) |>.set! (q 4) (byteOf R.D 1)
    |>.set! clo (byteOf R.D 2)

def reqRows (R : Run) (c : CReq) : Array (Array Nat) := Id.run do
  let usedA := R.used.getD c.cid #[]
  let mm := c.bits.length
  let valOf (pos : Nat) : Nat := R.base + R.D * (pos + 1) / 40
  let bm := c.bm.map (·.toNat)
  let mut out := #[]
  let mut jj := 0
  let mut curV := R.base
  for rho in List.range 20 do
    let yy := rho / 4
    let uu := rho % 4
    let pos := 8 * yy + 2 * uu
    let bb0 := b2n (getBit c.bm pos)
    let bb1 := b2n (getBit c.bm (pos + 1))
    let v0 := valOf pos
    let v1 := valOf (pos + 1)
    let cmV := if bb0 = 1 then v0 else curV
    let mut a := (zrow width).set! act 1 |>.set! kS 1 |>.set! fQ (b2n (rho == 0)) |>.set! tau R.tau
      |>.set! nn R.n |>.set! base R.base |>.set! dd R.D |>.set! cid c.cid
      |>.set! clo (c.cid % 256) |>.set! chi (c.cid / 256) |>.set! s c.s |>.set! r c.r
      |>.set! link c.link
    a := a.set! (q 0) (bm.getD yy 0 / 4 ^ uu)
    for i in [1, 2, 3, 4] do a := a.set! (q i) (bm.getD (yy + i) 0)
    a := a.set! b0 bb0 |>.set! b1 bb1 |>.set! u0 (bit uu 0) |>.set! u1 (bit uu 1) |>.set! y yy
      |>.set! iy (if yy = 4 then 0 else finv (fsub yy 4)) |>.set! e4 (b2n (yy == 4))
      |>.set! re (b2n (yy == 4 && uu == 3))
      |>.set! Q0 (R.D * (pos + 1) / 40) |>.set! Q1 (R.D * (pos + 2) / 40)
    for i in List.range 6 do
      a := a.set! (rb0 i) (bit (R.D * (pos + 1) % 40) i) |>.set! (rb1 i) (bit (R.D * (pos + 2) % 40) i)
    a := a.set! cur curV |>.set! cm cmV |>.set! j jj |>.set! m mm |>.set! key c.key
      |>.set! ikey (finv c.key) |>.set! zk0 (b2n (c.key == 0))
      |>.set! us0 (b2n (bb0 == 1 && usedA.getD jj false))
      |>.set! us1 (b2n (bb1 == 1 && usedA.getD (jj + bb0) false))
    out := out.push a
    jj := jj + bb0 + bb1
    curV := if bb1 = 1 then v1 else cmV
  return out

def rows (R : Run) : Array (Array Nat) :=
  if R.conv.isEmpty then #[] else
  R.conv.foldl (fun acc c => acc ++ reqRows R c) #[paramRow R]

def trace (R : Run) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  mkTrace (rows R) 1 fun _ => zrow width

def byte3 (x : Nat) : List Nat := [byteOf x 0, byteOf x 1, byteOf x 2]

/-- Public `SPAR` (tag 1) records received by the scan (one per instance with requests). -/
def expectedPar (I : Input) (tau : Nat := 0) : List (List Nat) :=
  let n := I.ids.length
  if (convRaw I.p n I.raw).isEmpty then [] else
  [[tau, 1, n] ++ byte3 I.p.base ++ byte3 (I.p.maxSingleGrant - I.p.base) ++ [0, 0]]

/-- Public `SRAW` records: raw requests with a set bit, numbered `cid = 0, 1, …`. -/
def expectedRaw (I : Input) (tau : Nat := 0) : List (List Nat) :=
  let rs := I.raw.filter fun q => !(setBits q.bm).isEmpty
  (List.range rs.length).zip rs |>.map fun (i, q) =>
    [tau, i % 256, i / 256, q.s, q.r] ++ (List.range 5).map fun b => (q.bm.getD b 0).toNat

end ZkFormal.NearV3.Sched.Gen.Scan
