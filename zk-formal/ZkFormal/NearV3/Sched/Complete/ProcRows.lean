import ZkFormal.NearV3.Sched.Complete.Trace
import ZkFormal.NearV3.Sched.Complete.MemRows
import ZkFormal.NearV3.Sched.Gen.Proc

/-!
# ZkFormal.NearV3.Sched.Complete.ProcRows — the honest process rows as value records (M4, `sprV3`)

* `PV`: the 64 cells of an `sprV3` row (`L i` = key-register limb `i`, columns `5 … 20`);
  `PV.cell` reads column `c`;
* records of the generator's rows: `keyV R k` (key block row `k < 16`), `hdrV R rd` (round
  header), `entV R rd es i` (entry `i` of the round, `es = rd.entries.toArray`; `le` on the last
  entry, `cx` = next entry's `ts`, or `T` on the last), `procVs R` = all rows; padding records
  `tailV R` (first padding row) and `padPV` (the others);
* `PRowRel a V`: array `a` has the 64 cells of `V`; **`proc_rows_rel`**: the generator's rows
  `Gen.Proc.rows R` are `procVs R`, row by row; `tail_rel`, `pad_rel` for the padding rows.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- The cells of a process row. -/
structure PV where
  act : Nat
  kK : Nat
  kH : Nat
  kE : Nat
  tau : Nat
  /-- key register limb `i` (column `5 + i`) -/
  L : Nat → Nat
  kc : Nat
  kl : Nat
  ikc : Nat
  kq : Nat
  Tq : Nat
  Kq : Nat
  zq : Nat
  K : Nat
  z : Nat
  zk : Nat
  iK : Nat
  kend : Nat
  Lr : Nat
  T : Nat
  x : Nat
  ts : Nat
  ein : Nat
  eout : Nat
  inc : Nat
  rem : Nat
  irem : Nat
  lastf : Nat
  s : Nat
  r : Nat
  link : Nat
  sbIn : Nat
  sbOut : Nat
  rbIn : Nat
  rbOut : Nat
  alIn : Nat
  alOut : Nat
  cS : Nat
  cR : Nat
  cL : Nat
  ok : Nat
  ia : Nat
  za : Nat
  zn : Nat
  pm : Nat
  le : Nat
  cg : Nat
  cx : Nat
  cy : Nat

namespace PV

def cell (X : PV) (c : Nat) : Nat :=
  if c = 0 then X.act
  else if c = 1 then X.kK
  else if c = 2 then X.kH
  else if c = 3 then X.kE
  else if c = 4 then X.tau
  else if c < 21 then X.L (c - 5)
  else if c = 21 then X.kc
  else if c = 22 then X.kl
  else if c = 23 then X.ikc
  else if c = 24 then X.kq
  else if c = 25 then X.Tq
  else if c = 26 then X.Kq
  else if c = 27 then X.zq
  else if c = 28 then X.K
  else if c = 29 then X.z
  else if c = 30 then X.zk
  else if c = 31 then X.iK
  else if c = 32 then X.kend
  else if c = 33 then X.Lr
  else if c = 34 then X.T
  else if c = 35 then X.x
  else if c = 36 then X.ts
  else if c = 37 then X.ein
  else if c = 38 then X.eout
  else if c = 39 then X.inc
  else if c = 40 then X.rem
  else if c = 41 then X.irem
  else if c = 42 then X.lastf
  else if c = 43 then X.s
  else if c = 44 then X.r
  else if c = 45 then X.link
  else if c = 46 then X.sbIn
  else if c = 47 then X.sbOut
  else if c = 48 then X.rbIn
  else if c = 49 then X.rbOut
  else if c = 50 then X.alIn
  else if c = 51 then X.alOut
  else if c = 52 then X.cS
  else if c = 53 then X.cR
  else if c = 54 then X.cL
  else if c = 55 then X.ok
  else if c = 56 then X.ia
  else if c = 57 then X.za
  else if c = 58 then X.zn
  else if c = 59 then X.pm
  else if c = 60 then X.le
  else if c = 61 then X.cg
  else if c = 62 then X.cx
  else if c = 63 then X.cy
  else 0

end PV

/-- All-zero record. -/
def zeroV : PV :=
  ⟨0, 0, 0, 0, 0, fun _ => 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Key block row `k` of instance `R.tau`. -/
def keyV (R : Run) (k : Nat) : PV :=
  { zeroV with
    act := 1, kK := 1, tau := R.tau, L := (fun i => keyLimb R.seed ((i + k) % 16)), kc := k,
    kl := b2n (k == 15), ikc := if k = 15 then 0 else finv (fsub k 15),
    sbIn := (R.seed.getD (2 * k) 0).toNat, sbOut := (R.seed.getD (2 * k + 1) 0).toNat,
    kq := 0, Tq := T0, Kq := Proc.KSENT, zq := 0 }

/-- Cells shared by a round's header and entries. -/
def baseV (R : Run) (rd : RoundD) : PV :=
  { zeroV with
    act := 1, tau := R.tau, L := (fun i => keyLimb R.seed ((i + 0) % 16)), ikc := Gen.Proc.ikcPad,
    K := rd.K, z := rd.z, zk := b2n (rd.K == 0), iK := finv rd.K, kend := rd.kend, Lr := rd.Lr,
    T := rd.T }

def hdrV (R : Run) (rd : RoundD) : PV :=
  { baseV R rd with
    kH := 1, kq := rd.kst, Tq := rd.T, Kq := rd.Kq, zq := rd.zq,
    cg := b2n (rd.K != 0), cx := rd.Kq, cy := rd.K + 1 }

def entV (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat) : PV :=
  { baseV R rd with
    kE := 1, kq := rd.kend, Tq := rd.T + rd.Lr, Kq := rd.K, zq := rd.z,
    x := es[i]!.x, ts := es[i]!.ts, ein := es[i]!.ein, eout := es[i]!.eout, inc := es[i]!.inc,
    rem := es[i]!.rem, irem := finv es[i]!.rem, lastf := b2n (es[i]!.rem == 0), s := es[i]!.s,
    r := es[i]!.r, link := es[i]!.link, sbIn := es[i]!.sbIn, sbOut := es[i]!.sbOut,
    rbIn := es[i]!.rbIn, rbOut := es[i]!.rbOut, alIn := es[i]!.alIn, alOut := es[i]!.alOut,
    cS := b2n es[i]!.cS, cR := b2n es[i]!.cR, cL := b2n es[i]!.cL, ok := b2n es[i]!.ok,
    ia := finv es[i]!.alOut, za := b2n (es[i]!.alOut == 0), zn := es[i]!.zn,
    pm := b2n (es[i]!.ok && !(es[i]!.rem == 0)), le := b2n (i + 1 == es.size), cg := 1,
    cx := if i + 1 == es.size then rd.T else es[i + 1]!.ts, cy := es[i]!.ts + 1 }

def roundVs (R : Run) (rd : RoundD) : List PV :=
  hdrV R rd :: (List.range rd.entries.toArray.size).map (entV R rd rd.entries.toArray)

def keyVs (R : Run) : List PV := (List.range 16).map (keyV R)

/-- All process rows of the instance. -/
def procVs (R : Run) : List PV := keyVs R ++ R.rounds.flatMap (roundVs R)

/-- The first padding row. -/
def tailV (R : Run) : PV :=
  { zeroV with
    tau := R.tau, L := (fun i => keyLimb R.seed ((i + 0) % 16)), ikc := Gen.Proc.ikcPad,
    kq := (match R.rounds.getLast? with | some rd => (rd.kend, rd.T + rd.Lr, rd.K, rd.z) | none => (0, T0, Proc.KSENT, 0)).1,
    Tq := (match R.rounds.getLast? with | some rd => (rd.kend, rd.T + rd.Lr, rd.K, rd.z) | none => (0, T0, Proc.KSENT, 0)).2.1,
    Kq := (match R.rounds.getLast? with | some rd => (rd.kend, rd.T + rd.Lr, rd.K, rd.z) | none => (0, T0, Proc.KSENT, 0)).2.2.1,
    zq := (match R.rounds.getLast? with | some rd => (rd.kend, rd.T + rd.Lr, rd.K, rd.z) | none => (0, T0, Proc.KSENT, 0)).2.2.2 }

/-- The other padding rows. -/
def padPV : PV := { zeroV with ikc := Gen.Proc.ikcPad }

/-! ## Arrays and records -/

/-- Array `a` has 64 cells, those of `V`. -/
def PRowRel (a : Array Nat) (V : PV) : Prop := (∀ c, c < 64 → gd a c = V.cell c) ∧ a.size = 64

theorem PRowRel.cell {a : Array Nat} {V : PV} (h : PRowRel a V) (c : Nat) : gd a c = V.cell c := by
  by_cases hc : c < 64
  · exact h.1 c hc
  · rw [gd_ge a (by rw [h.2]; omega)]
    unfold PV.cell
    repeat rw [if_neg (by omega)]

/-- The key register writes as sixteen explicit writes. -/
theorem withKey_eq (R : Run) (off : Nat) (a : Array Nat) :
    Gen.Proc.withKey R off a =
      ((((((((((((((((a).set! 5 (keyLimb R.seed ((0 + off) % 16))).set! 6 (keyLimb R.seed ((1 + off) % 16))).set! 7 (keyLimb R.seed ((2 + off) % 16))).set! 8 (keyLimb R.seed ((3 + off) % 16))).set! 9 (keyLimb R.seed ((4 + off) % 16))).set! 10 (keyLimb R.seed ((5 + off) % 16))).set! 11 (keyLimb R.seed ((6 + off) % 16))).set! 12 (keyLimb R.seed ((7 + off) % 16))).set! 13 (keyLimb R.seed ((8 + off) % 16))).set! 14 (keyLimb R.seed ((9 + off) % 16))).set! 15 (keyLimb R.seed ((10 + off) % 16))).set! 16 (keyLimb R.seed ((11 + off) % 16))).set! 17 (keyLimb R.seed ((12 + off) % 16))).set! 18 (keyLimb R.seed ((13 + off) % 16))).set! 19 (keyLimb R.seed ((14 + off) % 16))).set! 20 (keyLimb R.seed ((15 + off) % 16)) := by
  have hr : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  simp only [Gen.Proc.withKey, Id.run, List.forIn_pure_yield_eq_foldl, hr, List.foldl_cons, List.foldl_nil,
    Proc.colL, pure_bind]
  rfl

theorem size_withKey (R : Run) (off : Nat) (a : Array Nat) : (Gen.Proc.withKey R off a).size = a.size := by
  rw [withKey_eq]; simp only [size_set]

theorem keyRow_rel (R : Run) (k : Nat) : PRowRel (Gen.Proc.keyRow R k) (keyV R k) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 ∨ c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 ∨ c = 24 ∨ c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 ∨ c = 33 ∨ c = 34 ∨ c = 35 ∨ c = 36 ∨ c = 37 ∨ c = 38 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 44 ∨ c = 45 ∨ c = 46 ∨ c = 47 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52 ∨ c = 53 ∨ c = 54 ∨ c = 55 ∨ c = 56 ∨ c = 57 ∨ c = 58 ∨ c = 59 ∨ c = 60 ∨ c = 61 ∨ c = 62 ∨ c = 63) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [gd_setIf, Gen.Proc.keyRow, keyV, zeroV, PV.cell, withKey_eq, gd_set, gd_zrow, size_set, size_zrow,
      size_withKey, Proc.act, Proc.kK, Proc.kH, Proc.kE, Proc.tau, Proc.kc, Proc.kl, Proc.ikc, Proc.kq, Proc.Tq, Proc.Kq, Proc.zq, Proc.K, Proc.z, Proc.zk, Proc.iK, Proc.kend, Proc.Lr, Proc.T, Proc.x, Proc.ts, Proc.ein, Proc.eout, Proc.inc, Proc.rem, Proc.irem, Proc.lastf, Proc.s, Proc.r, Proc.link, Proc.sbIn, Proc.sbOut, Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.alOut, Proc.cS, Proc.cR, Proc.cL, Proc.ok, Proc.ia, Proc.za, Proc.zn, Proc.pm, Proc.le, Proc.cg, Proc.cx, Proc.cy, Proc.colL, Proc.width]
  · simp [Gen.Proc.keyRow, withKey_eq, size_set, size_zrow, size_withKey, Proc.width]

/-- The header array of the generator. -/
def hdrArr (R : Run) (rd : RoundD) : Array Nat :=
  (Gen.Proc.roundBase R rd).set! Proc.kH 1 |>.set! Proc.kq rd.kst |>.set! Proc.Tq rd.T |>.set! Proc.Kq rd.Kq
    |>.set! Proc.zq rd.zq |>.set! Proc.cg (b2n (rd.K != 0)) |>.set! Proc.cx rd.Kq |>.set! Proc.cy (rd.K + 1)

/-- The entry array of the generator (entry `i` of `es`). -/
def entArr (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat) : Array Nat :=
  (Gen.Proc.roundBase R rd).set! Proc.kE 1 |>.set! Proc.kq rd.kend |>.set! Proc.Tq (rd.T + rd.Lr)
    |>.set! Proc.Kq rd.K |>.set! Proc.zq rd.z |>.set! Proc.x es[i]!.x |>.set! Proc.ts es[i]!.ts
    |>.set! Proc.ein es[i]!.ein |>.set! Proc.eout es[i]!.eout |>.set! Proc.inc es[i]!.inc
    |>.set! Proc.rem es[i]!.rem |>.set! Proc.irem (finv es[i]!.rem) |>.set! Proc.lastf (b2n (es[i]!.rem == 0))
    |>.set! Proc.s es[i]!.s |>.set! Proc.r es[i]!.r |>.set! Proc.link es[i]!.link
    |>.set! Proc.sbIn es[i]!.sbIn |>.set! Proc.sbOut es[i]!.sbOut |>.set! Proc.rbIn es[i]!.rbIn
    |>.set! Proc.rbOut es[i]!.rbOut |>.set! Proc.alIn es[i]!.alIn |>.set! Proc.alOut es[i]!.alOut
    |>.set! Proc.cS (b2n es[i]!.cS) |>.set! Proc.cR (b2n es[i]!.cR) |>.set! Proc.cL (b2n es[i]!.cL)
    |>.set! Proc.ok (b2n es[i]!.ok) |>.set! Proc.ia (finv es[i]!.alOut) |>.set! Proc.za (b2n (es[i]!.alOut == 0))
    |>.set! Proc.zn es[i]!.zn |>.set! Proc.pm (b2n (es[i]!.ok && !(es[i]!.rem == 0)))
    |>.set! Proc.le (b2n (i + 1 == es.size)) |>.set! Proc.cg 1
    |>.set! Proc.cx (if i + 1 == es.size then rd.T else es[i + 1]!.ts) |>.set! Proc.cy (es[i]!.ts + 1)

theorem foldl_push_toList {α : Type} (f : Nat → α) : ∀ (l : List Nat) (acc : Array α),
    (l.foldl (fun out i => out.push (f i)) acc).toList = acc.toList ++ l.map f
  | [], acc => by simp
  | i :: l, acc => by rw [List.foldl_cons, foldl_push_toList f l]; simp

theorem roundRows_toList (R : Run) (rd : RoundD) :
    (Gen.Proc.roundRows R rd).toList =
      hdrArr R rd :: (List.range rd.entries.toArray.size).map (entArr R rd rd.entries.toArray) := by
  unfold Gen.Proc.roundRows
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  change (List.foldl (fun out i => out.push (entArr R rd rd.entries.toArray i)) #[hdrArr R rd]
    (List.range rd.entries.toArray.size)).toList = _
  rw [foldl_push_toList (entArr R rd rd.entries.toArray)]
  rfl

theorem hdrArr_rel (R : Run) (rd : RoundD) : PRowRel (hdrArr R rd) (hdrV R rd) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 ∨ c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 ∨ c = 24 ∨ c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 ∨ c = 33 ∨ c = 34 ∨ c = 35 ∨ c = 36 ∨ c = 37 ∨ c = 38 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 44 ∨ c = 45 ∨ c = 46 ∨ c = 47 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52 ∨ c = 53 ∨ c = 54 ∨ c = 55 ∨ c = 56 ∨ c = 57 ∨ c = 58 ∨ c = 59 ∨ c = 60 ∨ c = 61 ∨ c = 62 ∨ c = 63) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [gd_setIf, hdrArr, Gen.Proc.roundBase, hdrV, baseV, zeroV, PV.cell, withKey_eq, gd_set, gd_zrow, size_set, size_zrow,
      size_withKey, Proc.act, Proc.kK, Proc.kH, Proc.kE, Proc.tau, Proc.kc, Proc.kl, Proc.ikc, Proc.kq, Proc.Tq, Proc.Kq, Proc.zq, Proc.K, Proc.z, Proc.zk, Proc.iK, Proc.kend, Proc.Lr, Proc.T, Proc.x, Proc.ts, Proc.ein, Proc.eout, Proc.inc, Proc.rem, Proc.irem, Proc.lastf, Proc.s, Proc.r, Proc.link, Proc.sbIn, Proc.sbOut, Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.alOut, Proc.cS, Proc.cR, Proc.cL, Proc.ok, Proc.ia, Proc.za, Proc.zn, Proc.pm, Proc.le, Proc.cg, Proc.cx, Proc.cy, Proc.colL, Proc.width]
  · simp [hdrArr, Gen.Proc.roundBase, withKey_eq, size_set, size_zrow, size_withKey, Proc.width]

theorem entArr_rel (R : Run) (rd : RoundD) (es : Array Entry) (i : Nat) :
    PRowRel (entArr R rd es i) (entV R rd es i) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 ∨ c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 ∨ c = 24 ∨ c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 ∨ c = 33 ∨ c = 34 ∨ c = 35 ∨ c = 36 ∨ c = 37 ∨ c = 38 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 44 ∨ c = 45 ∨ c = 46 ∨ c = 47 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52 ∨ c = 53 ∨ c = 54 ∨ c = 55 ∨ c = 56 ∨ c = 57 ∨ c = 58 ∨ c = 59 ∨ c = 60 ∨ c = 61 ∨ c = 62 ∨ c = 63) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [gd_setIf, entArr, Gen.Proc.roundBase, entV, baseV, zeroV, PV.cell, withKey_eq, gd_set, gd_zrow, size_set, size_zrow,
      size_withKey, Proc.act, Proc.kK, Proc.kH, Proc.kE, Proc.tau, Proc.kc, Proc.kl, Proc.ikc, Proc.kq, Proc.Tq, Proc.Kq, Proc.zq, Proc.K, Proc.z, Proc.zk, Proc.iK, Proc.kend, Proc.Lr, Proc.T, Proc.x, Proc.ts, Proc.ein, Proc.eout, Proc.inc, Proc.rem, Proc.irem, Proc.lastf, Proc.s, Proc.r, Proc.link, Proc.sbIn, Proc.sbOut, Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.alOut, Proc.cS, Proc.cR, Proc.cL, Proc.ok, Proc.ia, Proc.za, Proc.zn, Proc.pm, Proc.le, Proc.cg, Proc.cx, Proc.cy, Proc.colL, Proc.width]
  · simp [entArr, Gen.Proc.roundBase, withKey_eq, size_set, size_zrow, size_withKey, Proc.width]

theorem tail_rel (R : Run) : PRowRel (Gen.Proc.tailRow R) (tailV R) := by
  unfold Gen.Proc.tailRow tailV
  cases R.rounds.getLast? with
  | none =>
      refine ⟨fun c hc => ?_, ?_⟩
      · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 ∨ c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 ∨ c = 24 ∨ c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 ∨ c = 33 ∨ c = 34 ∨ c = 35 ∨ c = 36 ∨ c = 37 ∨ c = 38 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 44 ∨ c = 45 ∨ c = 46 ∨ c = 47 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52 ∨ c = 53 ∨ c = 54 ∨ c = 55 ∨ c = 56 ∨ c = 57 ∨ c = 58 ∨ c = 59 ∨ c = 60 ∨ c = 61 ∨ c = 62 ∨ c = 63) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [gd_setIf, zeroV, zeroV, PV.cell, withKey_eq, gd_set, gd_zrow, size_set, size_zrow,
          size_withKey, Proc.act, Proc.kK, Proc.kH, Proc.kE, Proc.tau, Proc.kc, Proc.kl, Proc.ikc, Proc.kq, Proc.Tq, Proc.Kq, Proc.zq, Proc.K, Proc.z, Proc.zk, Proc.iK, Proc.kend, Proc.Lr, Proc.T, Proc.x, Proc.ts, Proc.ein, Proc.eout, Proc.inc, Proc.rem, Proc.irem, Proc.lastf, Proc.s, Proc.r, Proc.link, Proc.sbIn, Proc.sbOut, Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.alOut, Proc.cS, Proc.cR, Proc.cL, Proc.ok, Proc.ia, Proc.za, Proc.zn, Proc.pm, Proc.le, Proc.cg, Proc.cx, Proc.cy, Proc.colL, Proc.width]
      · simp [zeroV, withKey_eq, size_set, size_zrow, size_withKey, Proc.width]

  | some rd =>
      refine ⟨fun c hc => ?_, ?_⟩
      · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 ∨ c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 ∨ c = 24 ∨ c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 ∨ c = 33 ∨ c = 34 ∨ c = 35 ∨ c = 36 ∨ c = 37 ∨ c = 38 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 44 ∨ c = 45 ∨ c = 46 ∨ c = 47 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52 ∨ c = 53 ∨ c = 54 ∨ c = 55 ∨ c = 56 ∨ c = 57 ∨ c = 58 ∨ c = 59 ∨ c = 60 ∨ c = 61 ∨ c = 62 ∨ c = 63) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [gd_setIf, zeroV, zeroV, PV.cell, withKey_eq, gd_set, gd_zrow, size_set, size_zrow,
          size_withKey, Proc.act, Proc.kK, Proc.kH, Proc.kE, Proc.tau, Proc.kc, Proc.kl, Proc.ikc, Proc.kq, Proc.Tq, Proc.Kq, Proc.zq, Proc.K, Proc.z, Proc.zk, Proc.iK, Proc.kend, Proc.Lr, Proc.T, Proc.x, Proc.ts, Proc.ein, Proc.eout, Proc.inc, Proc.rem, Proc.irem, Proc.lastf, Proc.s, Proc.r, Proc.link, Proc.sbIn, Proc.sbOut, Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.alOut, Proc.cS, Proc.cR, Proc.cL, Proc.ok, Proc.ia, Proc.za, Proc.zn, Proc.pm, Proc.le, Proc.cg, Proc.cx, Proc.cy, Proc.colL, Proc.width]
      · simp [zeroV, withKey_eq, size_set, size_zrow, size_withKey, Proc.width]

theorem pad_rel : PRowRel ((zrow Proc.width).set! Proc.ikc Gen.Proc.ikcPad) padPV := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 ∨ c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 ∨ c = 24 ∨ c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 ∨ c = 33 ∨ c = 34 ∨ c = 35 ∨ c = 36 ∨ c = 37 ∨ c = 38 ∨ c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 42 ∨ c = 43 ∨ c = 44 ∨ c = 45 ∨ c = 46 ∨ c = 47 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52 ∨ c = 53 ∨ c = 54 ∨ c = 55 ∨ c = 56 ∨ c = 57 ∨ c = 58 ∨ c = 59 ∨ c = 60 ∨ c = 61 ∨ c = 62 ∨ c = 63) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [gd_setIf, padPV, zeroV, PV.cell, withKey_eq, gd_set, gd_zrow, size_set, size_zrow,
      size_withKey, Proc.act, Proc.kK, Proc.kH, Proc.kE, Proc.tau, Proc.kc, Proc.kl, Proc.ikc, Proc.kq, Proc.Tq, Proc.Kq, Proc.zq, Proc.K, Proc.z, Proc.zk, Proc.iK, Proc.kend, Proc.Lr, Proc.T, Proc.x, Proc.ts, Proc.ein, Proc.eout, Proc.inc, Proc.rem, Proc.irem, Proc.lastf, Proc.s, Proc.r, Proc.link, Proc.sbIn, Proc.sbOut, Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.alOut, Proc.cS, Proc.cR, Proc.cL, Proc.ok, Proc.ia, Proc.za, Proc.zn, Proc.pm, Proc.le, Proc.cg, Proc.cx, Proc.cy, Proc.colL, Proc.width]
  · simp [padPV, withKey_eq, size_set, size_zrow, size_withKey, Proc.width]

/-! ## Lists of rows -/

inductive PRRel : List (Array Nat) → List PV → Prop
  | nil : PRRel [] []
  | cons {a V L1 L2} : PRowRel a V → PRRel L1 L2 → PRRel (a :: L1) (V :: L2)

theorem PRRel.append {a b c d} (h1 : PRRel a b) (h2 : PRRel c d) : PRRel (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem PRRel.length {a b} (h : PRRel a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem PRRel.get {a b} (h : PRRel a b) : ∀ i (h1 : i < a.length) (h2 : i < b.length), PRowRel a[i] b[i] := by
  induction h with
  | nil => intro i h1; simp at h1
  | cons hr _ ih =>
    intro i h1 h2
    cases i with
    | zero => exact hr
    | succ i => exact ih i (by simpa using h1) (by simpa using h2)

theorem PRRel.map {α : Type} (f : α → Array Nat) (g : α → PV) (h : ∀ x, PRowRel (f x) (g x)) :
    ∀ l : List α, PRRel (l.map f) (l.map g)
  | [] => .nil
  | x :: l => .cons (h x) (PRRel.map f g h l)

theorem round_rel (R : Run) (rd : RoundD) : PRRel (Gen.Proc.roundRows R rd).toList (roundVs R rd) := by
  rw [roundRows_toList]
  exact .cons (hdrArr_rel R rd) (PRRel.map _ _ (entArr_rel R rd _) _)

theorem flat_round_rel (R : Run) : ∀ rds : List RoundD,
    PRRel (rds.flatMap fun rd => (Gen.Proc.roundRows R rd).toList) (rds.flatMap (roundVs R))
  | [] => .nil
  | rd :: rds => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (round_rel R rd).append (flat_round_rel R rds)

theorem foldl_append_toList' {α : Type} (f : α → Array (Array Nat)) :
    ∀ (l : List α) (acc : Array (Array Nat)),
      (l.foldl (fun acc x => acc ++ f x) acc).toList = acc.toList ++ l.flatMap (fun x => (f x).toList)
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_append_toList' f l, List.flatMap_cons, Array.toList_append, List.append_assoc]

/-- **The generated process rows are the records `procVs R`.** -/
theorem proc_rows_rel (R : Run) : PRRel (Gen.Proc.rows R).toList (procVs R) := by
  unfold Gen.Proc.rows procVs keyVs
  rw [foldl_append_toList']
  refine PRRel.append ?_ (flat_round_rel R R.rounds)
  simpa using PRRel.map (Gen.Proc.keyRow R) (keyV R) (keyRow_rel R) (List.range 16)

theorem procVs_length (R : Run) :
    (procVs R).length = 16 + (R.rounds.map fun rd => 1 + rd.entries.length).sum := by
  simp only [procVs, keyVs, List.length_append, List.length_map, List.length_range, List.length_flatMap,
    roundVs, List.length_cons, List.size_toArray]
  congr 1
  congr 1
  exact List.map_congr_left (fun _ _ => Nat.add_comm _ _)

end ZkFormal.NearV3.Sched.Complete
