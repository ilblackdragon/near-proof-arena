import ZkFormal.NearV3.Sched.Gen.Codec
/-! Pure row assignment builders extracted definitionally from the corrected
Codec generator. The core-refactor theorem establishes whole executable equality. -/
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAssignments
open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched.Codec
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
def headerRow (inst : List (Nat×Nat)) (params hdr : List Nat) (present : Bool) (p : Nat) : Array Nat :=
  let bp := hdr[p]!
  let regs := (List.range 32).map fun i => (reg i, params.getD (p+i) 0)
  let pb (x : Nat) := (List.range 8).map fun i => (pbit i, bit x i)
  let qb (x : Nat) := (List.range 8).map fun i => (prbit i, bit x i)
  ZkFormal.NearV3.Sched.Gen.setAll width (inst ++ [(kH, 1), (kF, if p = 0 then 1 else 0), (pos, p),
      (bpost, bp), (bpre, if present then bp else 0), (vbg, b2n present),
      (ihp, finv (fsub p 4)), (ehp, if p = 4 then 1 else 0)] ++ regs ++ pb bp ++ qb (if present then bp else 0))

def recordRow (I : Input) (present : Bool) (n kk f gg p bpo bpr : Nat) (inst extra : List (Nat×Nat)) : Array Nat :=
  let sender := kk/n
  let N := n*n
  let pb (x : Nat) := (List.range 8).map fun i => (pbit i, bit x i)
  ZkFormal.NearV3.Sched.Gen.setAll width (inst ++ [(kR, 1), (pos, p), (bpost, bpo), (bpre, bpr),
          (vbg, b2n present), (kidx, kk), (klo, kk % 256), (khi, kk / 256),
          (fS, if f = 0 then 1 else 0), (fR, if f = 1 then 1 else 0), (fA, if f = 2 then 1 else 0),
          (g, gg), (ig7, finv (fsub gg 7)), (e7, if gg = 7 then 1 else 0),
          (ikl, finv (fsub kk (N - 1))), (ekl, if kk + 1 = N then 1 else 0)] ++ pb bpo ++
          (if f=0 then (List.range 8).map (fun i=>(prbit i,(bytesLE (I.ids.getD sender 0) 8).getD (gg+i) 0)) else []) ++ extra)

def hashRow (inst : List (Nat×Nat)) (digest hpre : List Nat) (present : Bool) (base0 j : Nat) : Array Nat :=
  let bpr := hpre[j]!
  let regs := (List.range 32).map fun i => (reg i, digest.getD (j+i) 0)
  let pb (x : Nat) := (List.range 8).map fun i => (pbit i, bit x i)
  let qb (x : Nat) := (List.range 8).map fun i => (prbit i, bit x i)
  ZkFormal.NearV3.Sched.Gen.setAll width (inst ++ [(kZ, 1), (dgg, if j = 0 then 1 else 0), (pos, base0 + j), (sj, j), (bpost, digest[j]!),
      (bpre, if present then bpr else 0), (bsha, if present then bpr else 0), (vbg, b2n present),
      (isj, finv (fsub j 31)), (esj, if j = 31 then 1 else 0)] ++ regs ++ pb digest[j]! ++ qb (if present then bpr else 0))

def ashRow (inst : List (Nat×Nat)) (I : Input) (base0 j : Nat) : Array Nat :=
  let x := (I.ash.getD j 0).toNat
  ZkFormal.NearV3.Sched.Gen.setAll width (inst ++ [(kA, 1), (pos, base0 + 32 + j), (sj, 32 + j), (bsha, x),
      (pm0, j), (pm1, x), (isj, finv (fsub (32 + j) 63)), (esj, if j = 31 then 1 else 0)])
end ZkFormal.NearV3.Candidates.ProcPriorCodecAssignments
