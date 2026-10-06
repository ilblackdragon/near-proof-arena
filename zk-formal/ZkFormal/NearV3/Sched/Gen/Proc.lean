import ZkFormal.NearV3.Sched.Tables.Proc
import ZkFormal.NearV3.Sched.Gen.Run

/-!
# ZkFormal.NearV3.Sched.Gen.Proc — honest trace of the process table `sprV3`

Instance τ: the key block (row `kc`: register `Lᵢ = limb (i + kc) mod 16`, `sbIn, sbOut` = seed
bytes `2kc, 2kc+1`, `kq = 0, Tq = T0, Kq = KSENT, zq = 0`), then per round (`Run.rounds`) a
header (`kq = kst, Tq = T`, previous `Kq, zq`; `cx = Kq, cy = K + 1`) and its entries (`kq =
kend, Tq = T + Lr, Kq = K, zq = z` carried to the next header; `cx` = next `ts`, or `T` on the
last entry; `cy = ts + 1`). Inverse columns: `ikc = (kc − 15)⁻¹`, `iK = K⁻¹`, `irem = rem⁻¹`,
`ia = alOut⁻¹` (0 for 0). Padding: the first padding row carries the key register and the
instance carries (`kq, Tq, Kq, zq, τ`) of the last row; `ikc = (−15)⁻¹` on every padding row.

Expected public traffic: `SPUBB (τ, 3, k, seed[2k], seed[2k+1], 0, 0)`, `k < 16`.
-/

namespace ZkFormal.NearV3.Sched.Gen.Proc

open ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Proc (act kK kH kE tau colL kc kl ikc kq Tq Kq zq K z zk iK kend Lr T x ts
  ein eout inc rem irem lastf s r link sbIn sbOut rbIn rbOut alIn alOut cS cR cL ok ia za zn pm le cg
  cx cy width KSENT)

def ikcPad : Nat := finv (fneg 15)

/-- Row with the key register `Lᵢ = limb (i + off) mod 16`. -/
def withKey (R : Run) (off : Nat) (a : Array Nat) : Array Nat := Id.run do
  let mut a := a
  for i in List.range 16 do a := a.set! (colL i) (keyLimb R.seed ((i + off) % 16))
  return a

def keyRow (R : Run) (k : Nat) : Array Nat :=
  withKey R k <| (zrow width).set! act 1 |>.set! kK 1 |>.set! tau R.tau |>.set! kc k
    |>.set! kl (b2n (k == 15)) |>.set! ikc (if k = 15 then 0 else finv (fsub k 15))
    |>.set! sbIn (R.seed.getD (2 * k) 0).toNat |>.set! sbOut (R.seed.getD (2 * k + 1) 0).toNat
    |>.set! kq 0 |>.set! Tq T0 |>.set! Kq KSENT |>.set! zq 0

/-- Columns shared by a round's header and entries. -/
def roundBase (R : Run) (rd : RoundD) : Array Nat :=
  withKey R 0 <| (zrow width).set! act 1 |>.set! tau R.tau |>.set! ikc ikcPad |>.set! K rd.K
    |>.set! z rd.z |>.set! zk (b2n (rd.K == 0)) |>.set! iK (finv rd.K) |>.set! kend rd.kend
    |>.set! Lr rd.Lr |>.set! T rd.T

def roundRows (R : Run) (rd : RoundD) : Array (Array Nat) := Id.run do
  let b := roundBase R rd
  let mut out := #[b.set! kH 1 |>.set! kq rd.kst |>.set! Tq rd.T |>.set! Kq rd.Kq |>.set! zq rd.zq
    |>.set! cg (b2n (rd.K != 0)) |>.set! cx rd.Kq |>.set! cy (rd.K + 1)]
  let es := rd.entries.toArray
  for i in List.range es.size do
    let e := es[i]!
    let last := i + 1 == es.size
    let lastF := e.rem == 0
    out := out.push (b.set! kE 1 |>.set! kq rd.kend |>.set! Tq (rd.T + rd.Lr) |>.set! Kq rd.K
      |>.set! zq rd.z |>.set! x e.x |>.set! ts e.ts |>.set! ein e.ein |>.set! eout e.eout
      |>.set! inc e.inc |>.set! rem e.rem |>.set! irem (finv e.rem) |>.set! lastf (b2n lastF)
      |>.set! s e.s |>.set! r e.r |>.set! link e.link |>.set! sbIn e.sbIn |>.set! sbOut e.sbOut
      |>.set! rbIn e.rbIn |>.set! rbOut e.rbOut |>.set! alIn e.alIn |>.set! alOut e.alOut
      |>.set! cS (b2n e.cS) |>.set! cR (b2n e.cR) |>.set! cL (b2n e.cL) |>.set! ok (b2n e.ok)
      |>.set! ia (finv e.alOut) |>.set! za (b2n (e.alOut == 0)) |>.set! zn e.zn
      |>.set! pm (b2n (e.ok && !lastF)) |>.set! le (b2n last) |>.set! cg 1
      |>.set! cx (if last then rd.T else es[i + 1]!.ts) |>.set! cy (e.ts + 1))
  return out

def rows (R : Run) : Array (Array Nat) :=
  R.rounds.foldl (fun acc rd => acc ++ roundRows R rd) ((List.range 16).toArray.map (keyRow R))

/-- The first padding row: key register and instance carries of the last row. -/
def tailRow (R : Run) : Array Nat :=
  let (kq0, Tq0, Kq0, zq0) := match R.rounds.getLast? with
    | some rd => (rd.kend, rd.T + rd.Lr, rd.K, rd.z)
    | none => (0, T0, KSENT, 0)
  withKey R 0 <| (zrow width).set! tau R.tau |>.set! ikc ikcPad |>.set! kq kq0 |>.set! Tq Tq0
    |>.set! Kq Kq0 |>.set! zq zq0

def trace (R : Run) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  let rs := rows R
  mkTrace rs 1 fun i => if i = rs.size then tailRow R else (zrow width).set! ikc ikcPad

/-- Public key records `(τ, 3, k, lo, hi, 0, 0)` received by the key block. -/
def expectedKey (seed : List UInt8) (tau : Nat := 0) : List (List Nat) :=
  (List.range 16).map fun k => [tau, TAG_KEY, k, (seed.getD (2 * k) 0).toNat, (seed.getD (2 * k + 1) 0).toNat, 0, 0]

end ZkFormal.NearV3.Sched.Gen.Proc
