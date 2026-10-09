import ZkFormal.NearV3.Candidates.ProcPriorCodecLoopTotal
import ZkFormal.NearV3.Candidates.ProcActualRunProjection
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecWrapperTotal
open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched.Codec
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
def core (I : Input) (R : Run) (present : Bool) (vidV : Nat) (gbA : Array Nat)
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
  let recs ← forIn (List.range N) (rows,cmps)
    (ProcPriorCodecLoopTotal.recordStep I R present gbA fwd inst)
  rows := recs.1
  cmps := recs.2
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


theorem codec_eq (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) :
    ProcPriorCodecGen.codecRows I R present vid gb fwd =
      (core I R present vid gb fwd).map (ProcPriorCodecGen.install I R present) := rfl

theorem append_success (α : Type) (xs : List α) (f : α → Array Nat) (s : Array (Array Nat)) :
    ∃out,forIn xs s (fun x rows=>(.ok (.yield (rows.push (f x))) : Except String (ForInStep (Array (Array Nat)))))=.ok out := by
  induction xs generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons x xs ih =>
    simpa only [List.forIn_cons,bind,Except.bind] using ih (s.push (f x))
theorem core_success (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat))
    (ha : ∀k,k<R.n*R.n → ProcPriorCodecLoopTotal.Allowance I R present k)
    (hf : ∀k,k<R.n*R.n → R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,core I R present vidV gb fwd=.ok out := by
  let n := R.n
  let N := n*n
  let tv := R.tau
  let fairV := I.p.maxShardBandwidth/n
  let baseV := I.p.base
  let hpre := if present then I.prev.sanityHash.map (·.toNat) else List.replicate 32 0
  let shaIn := hpre++I.ash.map (·.toNat)
  let digest := (NearSpec.sha256 (shaIn.map UInt8.ofNat)).map (·.toNat)
  let hdr : List Nat := [0,N%256,N/256%256,0,0]
  let params := hdr++bytesLE baseV 3++bytesLE fairV 3
  let inst : List (Nat×Nat) := [(act,1),(tau,tv),(pres,b2n present),(vid,vidV),(nn,n),
    (NN,N),(base,baseV),(fair,fairV),(itz,finv tv),(zt,if tv=0 then 1 else 0)]
  obtain ⟨a,ha'⟩ := append_success Nat (List.range 5)
    (ProcPriorCodecAssignments.headerRow inst params hdr present) #[]
  obtain ⟨b,hb⟩ := ProcPriorCodecLoopTotal.records_success I R present gb fwd inst
    (List.range N) (a,[]) (fun k hk=>ha k (List.mem_range.mp hk))
    (fun k hk=>hf k (List.mem_range.mp hk))
  obtain ⟨c,hc⟩ := append_success Nat (List.range 32)
    (ProcPriorCodecAssignments.hashRow inst digest hpre present (5+24*N)) b.1
  obtain ⟨d,hd⟩ := append_success Nat (List.range 32)
    (ProcPriorCodecAssignments.ashRow inst I (5+24*N)) c
  unfold core
  dsimp only
  simp only [pure,Except.pure]
  dsimp only [inst,params,hdr,baseV,fairV,tv,n,N,digest,shaIn,hpre] at ha' hb hc hd
  rw [ha']
  simp only [bind,Except.bind]
  rw [hb]
  simp only [bind,Except.bind]
  rw [hc]
  simp only [bind,Except.bind]
  rw [hd]
  exact ⟨_,rfl⟩

theorem codec_success (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat))
    (ha : ∀k,k<R.n*R.n → ProcPriorCodecLoopTotal.Allowance I R present k)
    (hf : ∀k,k<R.n*R.n → R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out := by
  obtain ⟨out,ho⟩ := core_success I R present vid gb fwd ha hf
  exact ⟨ProcPriorCodecGen.install I R present out,by rw [codec_eq,ho]; rfl⟩
set_option maxHeartbeats 600000 in
theorem run_a2 (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R) :
    R.a2=(linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).a2 := by
  unfold ActualRun.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals rfl

theorem run_codec_success (I : Input) (tau : Nat) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat))
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (hr : ActualRun.run I tau=.ok R)
    (hz : present=false → ∀(k : Nat),(ProcActualInput.allowances I.ids I.prev)[k]! = 0)
    (hf : ∀k,k<R.n*R.n → R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃out,ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out := by
  apply codec_success I R present vid gb fwd ?_ hf
  intro k hk
  have hn := (ProcActualRunProjection.run_fields I tau R hr).2.1
  have he := ProcPriorCodecAllowanceGuard.record_allowance I R present k
    (ProcPriorCodecCarryTotal.bit I R present k) hn hk hp (run_a2 I tau R hr)
    (fun h=>hz h k) rfl
  simpa [ProcPriorCodecLoopTotal.Allowance,ProcPriorCodecRecordTotal.endAllowance,
    ProcPriorCodecCarryTotal.bit] using he
end ZkFormal.NearV3.Candidates.ProcPriorCodecWrapperTotal
