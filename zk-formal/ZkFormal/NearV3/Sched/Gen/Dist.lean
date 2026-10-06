import ZkFormal.NearV3.Sched.Gen.Run
import ZkFormal.NearV3.Sched.Tables.Dist
import ZkFormal.NearV3.Sched.Render

/-!
# ZkFormal.NearV3.Sched.Gen.Dist — honest rows of `sdsV3` (one instance)

Shard rows (senders, then receivers, each in sorted order by `avg·64 + shard`), then for each
sender position a header and the `n` cells. Values from the run's final budgets (after the
process phase) and the claim-only counts; grants recomputed on the grid and returned per link.
-/

namespace ZkFormal.NearV3.Sched.Gen

open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched.Dist

structure DistOut where
  rows : Array (Array Nat)
  /-- grid grant per link (`0` on disallowed links) -/
  gb : Array Nat
  /-- comparator messages `(x, y, b)` -/
  cmps : List (Nat × Nat × Nat)

def setAll (w : Nat) (kv : List (Nat × Nat)) : Array Nat :=
  kv.foldl (fun r (c, v) => r.set! c v) (zrow w)

def bitsOf (col : Nat → Nat) (x : Nat) : List (Nat × Nat) :=
  (List.range 6).map fun i => (col i, bit x i)

def distRows (I : Input) (R : Run) : Except String DistOut := do
  let n := R.n
  let tv := R.tau
  let alf (l : Nat) : Bool := I.allowed[l]!
  let cS := fun s => cntS n I.allowed s
  let cR := fun r => cntR n I.allowed r
  let sb := R.fin.sb
  let rb := R.fin.rb
  let avg (c left : Nat) : Nat := if c = 0 then 0 else left / c
  let sord := sortByKey (fun s => avg (cS s) sb[s]!) (List.range n)
  let rord := sortByKey (fun r => avg (cR r) rb[r]!) (List.range n)
  let mut rows : Array (Array Nat) := #[]
  let mut cmps : List (Nat × Nat × Nat) := []
  let cmpOf (x y : Nat) : Nat × Nat × Nat := (x, y, if y ≤ x then 1 else 0)
  -- shard rows
  for sd in [0, 1] do
    let ord := if sd = 0 then sord else rord
    let mut kpv := 0
    for i in List.range n do
      let x := ord[i]!
      let c := if sd = 0 then cS x else cR x
      let left := if sd = 0 then sb[x]! else rb[x]!
      let b0 := (budget0 ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩ sd x)
      let q := avg c left
      let rem := if c = 0 then 0 else left % c
      let key := q * 64 + x
      check (kpv ≤ key) "sort order"
      cmps := cmps ++ [cmpOf key kpv]
      let e1v := if i + 1 = n then 1 else 0
      rows := rows.push (setAll width ([(act, 1), (kSh, 1), (tau, tv), (nn, n), (side, sd), (a, i),
        (r, x), (N2, c), (L2, left), (by0, b0 % 256), (by1, b0 / 256 % 256), (by2, b0 / 65536 % 256),
        (q2, q), (r2, rem), (icnt, finv c), (zc, if c = 0 then 1 else 0), (kp, kpv),
        (da, if sd = 0 then i else 0), (db, if sd = 0 then 255 else i), (cx, key), (cy, kpv),
        (cb, 1), (cg, 1), (dlsg, 1), (sL, left), (e1, e1v),
        (ig1, finv (fsub i (n - 1)))] ++ (if c = 0 then [] else bitsOf bt2 (c - 1 - rem))))
      kpv := key + 1
  -- grid
  let mut gbArr : Array Nat := Array.replicate (n * n) 0
  let mut ri : Array (Nat × Nat) := (List.range n).toArray.map fun r => (cR r, rb[r]!)
  for i in List.range n do
    let sv := sord[i]!
    let mut se := (cS sv, sb[sv]!)
    -- header: receives the sender endpoint into (r, N2, L2)
    rows := rows.push (setAll width [(act, 1), (kGH, 1), (tau, tv), (nn, n), (a, i), (b, 255),
      (r, sv), (N2, se.1), (L2, se.2), (dlrg, 1)])
    for j in List.range n do
      let rr := rord[j]!
      let l := sv * n + rr
      let re := ri[rr]!
      let alv := alf l
      let (q1v, r1v, q2v, r2v, gbv) :=
        if alv then
          let q1v := se.2 / se.1
          let q2v := re.2 / re.1
          (q1v, se.2 % se.1, q2v, re.2 % re.1, Nat.min q1v q2v)
        else (0, 0, 0, 0, 0)
      if alv then
        check (se.1 ≥ 1 && re.1 ≥ 1) "distribute break"
        cmps := cmps ++ [cmpOf q1v q2v]
      let cbv := if alv && q2v ≤ q1v then 1 else 0
      let N2' := re.1 - (if alv then 1 else 0)
      let L2' := re.2 - gbv
      let e1v := if j + 1 = n then 1 else 0
      let e2v := if i + 1 = n then 1 else 0
      rows := rows.push (setAll width ([(act, 1), (kC, 1), (tau, tv), (nn, n), (a, i), (b, j), (s, sv),
        (r, rr), (N1, se.1), (L1, se.2), (N2, re.1), (L2, re.2), (q1, q1v), (r1, r1v), (q2, q2v),
        (r2, r2v), (llo, l % 256), (lhi, l / 256), (al, b2n alv), (gb, gbv), (cx, q1v), (cy, q2v),
        (cb, cbv), (cg, b2n alv), (da, i + 1), (db, j), (sL, L2'), (dlsg, 1 - e2v), (dlrg, 1),
        (e1, e1v), (ig1, finv (fsub j (n - 1))), (e2, e2v), (ig2, finv (fsub i (n - 1))),
        (eI, e1v * e2v)] ++
        (if alv then bitsOf bt1 (se.1 - 1 - r1v) ++ bitsOf bt2 (re.1 - 1 - r2v) else [])))
      if alv then
        gbArr := gbArr.set! l gbv
        se := (se.1 - 1, se.2 - gbv)
      ri := ri.set! rr (N2', L2')
  return ⟨rows, gbArr, cmps⟩

/-- Padding row of `sdsV3` (all zero). -/
def distPad (_ : Nat) : Array Nat := zrow width

end ZkFormal.NearV3.Sched.Gen
