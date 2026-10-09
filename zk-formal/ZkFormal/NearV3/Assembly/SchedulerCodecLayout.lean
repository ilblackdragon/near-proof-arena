import ZkFormal.NearV3.Assembly.SchedulerCodecLoops
import ZkFormal.NearV3.Candidates.ProcPriorCodecGen

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched.Codec
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Candidates

/-! A transparent proof view of the private imperative core. The equality
below is definitional and preserves every byte, error, comparator and row. -/
def coreLayout (I : Input) (R : Run) (present : Bool) (vidV : Nat) (gbA : Array Nat)
    (fwd : List (Nat × Nat)) : Except String CodecOut := do
  let n := R.n
  let N := n * n
  let tv := R.tau
  let P : InstPub := ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩
  let fairV := I.p.maxShardBandwidth / n
  let baseV := I.p.base
  let a0 := Array.replicate N 0
  let hpre : List Nat := if present then I.prev.sanityHash.map (·.toNat) else List.replicate 32 0
  let shaIn := hpre ++ I.ash.map (·.toNat)
  let digest := (NearSpec.sha256 (shaIn.map UInt8.ofNat)).map (·.toNat)
  let segL (k : Nat) : ZkFormal.NearV3.Sched.Gen.Seg := R.segs.getD k default
  let afinF (k : Nat) : Nat := (segL k).vfin
  let gfinF (k : Nat) : Nat := (segL k).wfin
  let pre := if present then I.prev.encode.map (·.toNat) else []
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
    rows := rows.push (ProcPriorCodecAssignments.headerRow inst params hdr present p)
  -- records
  for kk in List.range N do
    for f in List.range 3 do
      let mut apv := 0
      let mut apostv := 0
      let mut bigv := 0
      let mut cbv := 0
      let recState ← forIn (List.range 8) (rows,cmps,apv,apostv,bigv,cbv)
        (fun gg st => ProcPriorCodecRecordStep.step I R present gbA fwd inst kk f gg st)
      rows := recState.1
      cmps := recState.2.1
      apv := recState.2.2.1
      apostv := recState.2.2.2.1
      bigv := recState.2.2.2.2.1
      cbv := recState.2.2.2.2.2
  -- hash rows
  let base0 := 5 + 24 * N
  for j in List.range 32 do
    let bpr := hpre[j]!
    let regs := (List.range 32).map fun i => (reg i, digest.getD (j + i) 0)
    rows := rows.push (ProcPriorCodecAssignments.hashRow inst digest hpre present base0 j)
  for j in List.range 32 do
    let x := (I.ash.getD j 0).toNat
    rows := rows.push (ProcPriorCodecAssignments.ashRow inst I base0 j)
  return ⟨rows, pre, post, cmps, shaIn, digest⟩

theorem coreLayout_eq (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) :
    (coreLayout I R present vidV gbA fwd).map (ProcPriorCodecGen.install I R present)=
      ProcPriorCodecGen.codecRows I R present vidV gbA fwd := rfl

end ZkFormal.NearV3.Assembly.CodecDigest
