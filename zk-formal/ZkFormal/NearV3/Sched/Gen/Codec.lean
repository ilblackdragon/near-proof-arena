import ZkFormal.NearV3.Sched.Gen.Run
import ZkFormal.NearV3.Sched.Tables.Codec
import ZkFormal.NearV3.Sched.Render
import ZkFormal.NearV3.Sched.Gen.Dist

/-!
# ZkFormal.NearV3.Sched.Gen.Codec — honest rows of `schV3` (one instance)

Header (5), records (`24·N`), hash (32) and `sha256(all_shards)` (32) rows of instance `τ`,
from the canonical previous state (or absent), the run's link pass and final memory values, the
grid grants, and the forwarding demands of instance 0.
-/

namespace ZkFormal.NearV3.Sched.Gen

open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched.Codec

structure CodecOut where
  rows : Array (Array Nat)
  pre : List Nat
  post : List Nat
  cmps : List (Nat × Nat × Nat)
  shaIn : List Nat
  digest : List Nat

def bytesLE (x len : Nat) : List Nat := (List.range len).map fun i => x / 256 ^ i % 256

/-- Canonical state bytes for allowances `a` and hash `h`. -/
def stateBytes (ids : List Nat) (a : Nat → Nat) (h : List Nat) : List Nat :=
  let n := ids.length
  let N := n * n
  [0] ++ bytesLE N 4 ++ (List.range N).flatMap (fun k =>
    bytesLE (ids.getD (k / n) 0) 8 ++ bytesLE (ids.getD (k % n) 0) 8 ++ bytesLE (a k) 8) ++ h

def codecRows (I : Input) (R : Run) (present : Bool) (vidV : Nat) (gbA : Array Nat)
    (fwd : List (Nat × Nat)) : Except String CodecOut := do
  let n := R.n
  let N := n * n
  let tv := R.tau
  let P : InstPub := ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩
  let fairV := I.p.maxShardBandwidth / n
  let baseV := I.p.base
  let a0 := a0Canon n I.prev
  let hpre : List Nat := if present then I.prev.sanityHash.map (·.toNat) else List.replicate 32 0
  let shaIn := hpre ++ I.ash.map (·.toNat)
  let digest := (NearSpec.sha256 (shaIn.map UInt8.ofNat)).map (·.toNat)
  let segL (k : Nat) : Seg := R.segs.getD k default
  let afinF (k : Nat) : Nat := (segL k).vfin
  let gfinF (k : Nat) : Nat := (segL k).wfin
  let pre := if present then stateBytes I.ids (fun k => a0[k]!) hpre else []
  let post := stateBytes I.ids afinF digest
  let hdr : List Nat := [0, N % 256, N / 256 % 256, 0, 0]
  let params : List Nat := hdr ++ bytesLE baseV 3 ++ bytesLE fairV 3
  let mut rows : Array (Array Nat) := #[]
  let mut cmps : List (Nat × Nat × Nat) := []
  let inst : List (Nat × Nat) := [(act, 1), (tau, tv), (pres, b2n present), (vid, vidV), (nn, n),
    (NN, N), (base, baseV), (fair, fairV), (itz, finv tv), (zt, if tv = 0 then 1 else 0)]
  let pb (x : Nat) : List (Nat × Nat) := (List.range 8).map fun i => (pbit i, bit x i)
  let qb (x : Nat) : List (Nat × Nat) := (List.range 8).map fun i => (prbit i, bit x i)
  -- header
  for p in List.range 5 do
    let bp := hdr[p]!
    let regs := (List.range 32).map fun i => (reg i, params.getD (p + i) 0)
    rows := rows.push (setAll width (inst ++ [(kH, 1), (kF, if p = 0 then 1 else 0), (pos, p),
      (bpost, bp), (bpre, if present then bp else 0), (vbg, b2n present),
      (ihp, finv (fsub p 4)), (ehp, if p = 4 then 1 else 0)] ++ regs ++ pb bp ++ qb (if present then bp else 0)))
  -- records
  for kk in List.range N do
    for f in List.range 3 do
      let mut apv := 0
      let mut apostv := 0
      let mut bigv := 0
      let mut cbv := 0
      for gg in List.range 8 do
        let p := 5 + 24 * kk + 8 * f + gg
        let bpo := if f < 2 then idByte I.ids kk (8 * f + gg) else (if gg < 3 then afinF kk / 256 ^ gg % 256 else 0)
        let bpr := if ¬present then 0 else if f < 2 then bpo else a0[kk]! / 256 ^ gg % 256
        let lowfv := if gg < 3 then 1 else 0
        let wtv := 256 ^ gg
        let nzbv := if bpr = 0 then 0 else 1
        let isEnd := f = 2 ∧ gg = 7
        let mut extra : List (Nat × Nat) := []
        if f = 2 then
          extra := extra ++ [(lowf, lowfv), (wt, wtv % ZkFormal.Algebra.P), (ap, apv), (big, bigv), (apost, apostv),
            (nzb, nzbv), (ib, finv bpr), (ig2, finv (fsub gg 2)), (e2, if gg = 2 then 1 else 0)]
          if gg = 2 then
            let x := apv + wtv * bpr + fairV
            cbv := if Codec.MA ≤ x then 1 else 0
            cmps := cmps ++ [(x, Codec.MA, cbv)]
            extra := extra ++ [(cx, x), (cy, Codec.MA), (cbit, cbv), (cg, 1)]
          if gg ≥ 2 then extra := extra ++ [(cb, cbv)]
        if isEnd then
          let bFv := if bigv = 1 ∨ nzbv = 1 then 1 else 0
          let a1v := if bFv = 1 then Codec.MA else (if cbv = 1 then Codec.MA else apv + fairV)
          let alv := b2n (I.allowed[kk]!)
          let a2v := a1v - alv * baseV
          check (a2v == R.a2[kk]!) "codec a2 differs from the link pass"
          let gbv := gbA[kk]!
          let gf := gfinF kk
          let lastRec := kk + 1 = N
          extra := extra ++ [(rend, 1), (bF, bFv), (a1, a1v), (al, alv), (a2, a2v), (g2, alv * baseV),
            (afin, afinF kk), (gfin, gf), (gb, gbv), (dgg, if lastRec then 1 else 0)]
          if lastRec then
            extra := extra ++ (List.range 32).map fun i => (reg i, digest[i]!)
          if tv = 0 then
            let ft := ((fwd.find? (·.1 == kk)).map (·.2)).getD 0
            check (ft ≤ gf + gbv) "forwarding demand above the grant"
            cmps := cmps ++ [(gf + gbv, ft, 1)]
            extra := extra ++ [(fwg, 1), (cx, gf + gbv), (cy, ft), (cbit, 1), (cg, 1), (pm0, kk % 256),
              (pm1, kk / 256), (fb 0, ft % 256), (fb 1, ft / 256 % 256), (fb 2, ft / 65536 % 256)]
        rows := rows.push (setAll width (inst ++ [(kR, 1), (pos, p), (bpost, bpo), (bpre, bpr),
          (vbg, b2n present), (kidx, kk), (klo, kk % 256), (khi, kk / 256),
          (fS, if f = 0 then 1 else 0), (fR, if f = 1 then 1 else 0), (fA, if f = 2 then 1 else 0),
          (g, gg), (ig7, finv (fsub gg 7)), (e7, if gg = 7 then 1 else 0),
          (ikl, finv (fsub kk (N - 1))), (ekl, if kk + 1 = N then 1 else 0)] ++ pb bpo ++ qb bpr ++ extra))
        if f = 2 ∧ gg < 3 then
          apv := apv + wtv * bpr
          apostv := apostv + wtv * bpo
        if f = 2 ∧ gg ≥ 3 ∧ bpr ≠ 0 then bigv := 1
  -- hash rows
  let base0 := 5 + 24 * N
  for j in List.range 32 do
    let bpr := hpre[j]!
    let regs := (List.range 32).map fun i => (reg i, digest.getD (j + i) 0)
    rows := rows.push (setAll width (inst ++ [(kZ, 1), (pos, base0 + j), (sj, j), (bpost, digest[j]!),
      (bpre, if present then bpr else 0), (bsha, if present then bpr else 0), (vbg, b2n present),
      (isj, finv (fsub j 31)), (esj, if j = 31 then 1 else 0)] ++ regs ++ pb digest[j]! ++ qb (if present then bpr else 0)))
  for j in List.range 32 do
    let x := (I.ash.getD j 0).toNat
    rows := rows.push (setAll width (inst ++ [(kA, 1), (pos, base0 + 32 + j), (sj, 32 + j), (bsha, x),
      (pm0, j), (pm1, x), (isj, finv (fsub (32 + j) 63)), (esj, if j = 31 then 1 else 0)]))
  return ⟨rows, pre, post, cmps, shaIn, digest⟩

def codecPad (_ : Nat) : Array Nat := zrow width

end ZkFormal.NearV3.Sched.Gen
