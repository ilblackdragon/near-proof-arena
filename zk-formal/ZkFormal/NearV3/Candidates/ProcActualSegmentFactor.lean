import ZkFormal.NearV3.Candidates.ProcActualSegments
namespace ZkFormal.NearV3.Candidates.ProcActualSegmentFactor
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound
def afterMemory (I : Input) (tau : Nat) (conv : Array CReq) (stF : PState) (acc : Acc)
    (segs : Array Gen.Seg) (cs : ProcActualMemoryScan.Cmps) : Except String Run := do
  let n := I.ids.length
  let p := I.p
  let lp := linkPass n p I.allowed (ProcActualInput.allowances I.ids I.prev)
  let key := NearSpecV3.leWords I.seed
  let (_,_,_,_,_,_,_,_,_,_,kpos,_,_,used,rounds,_) := acc
  let cmpOf (x y : Nat) : Nat×Nat×Nat := (x,y,if y≤x then 1 else 0)
  let mut cmps := cs
  for rd in rounds do
    if rd.K != 0 then
      check (rd.K < rd.Kq) "round keys not decreasing"
      cmps := cmps.push (cmpOf rd.Kq (rd.K + 1))
    let es := rd.entries.toArray
    for i in List.range es.size do
      let e := es[i]!
      let cx := if i + 1 = es.size then rd.T else es[i + 1]!.ts
      check (e.ts < cx) "bucket ts order"
      cmps := cmps.push (cmpOf cx (e.ts + 1))
  check (cmps.all fun (x, y, _) => x < 2 ^ 29 && y < 2 ^ 29) "comparison operand ≥ 2^29"
  let D := p.maxSingleGrant - p.base
  check (p.base < 2 ^ 24 && D < 2 ^ 24) "params ≥ 2^24"
  return { tau, n, base := p.base, D, seed := I.seed, key, a2 := lp.a2, conv := conv.toList,
           used, rounds := rounds.toList, segs := segs.toList, cmps := cmps.toList,
           kfin := kpos, fin := stF }
def finishSegments (I : Input) (tau : Nat) (conv : Array CReq) (stF : PState) (acc : Acc) : Except String Run := do
  let (sb,rb,aa,gg,_,_,_,pushes,bucketsAll,_,kpos,_,_,_,_,_) := acc
  -- every push is popped exactly once
  check (sortPush pushes.toList == sortPush bucketsAll.toList) "push log ≠ buckets"
  -- final state
  check (sb == stF.sb && rb == stF.rb && aa == stF.al && gg == stF.g) "final state differs"
  check (kpos == rngPos stF.rng) "final RNG position differs"
  let segs ← ProcActualSegments.build I tau acc
  let cs ← forIn segs (#[] : ProcActualMemoryScan.Cmps) ProcActualMemoryScan.segmentStep
  afterMemory I tau conv stF acc segs cs

theorem finish_eq (I : Input) (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc) :
    ProcActualMemoryFactor.finishMemory I tau cv st s=finishSegments I tau cv st s := by
  simp only [ProcActualMemoryFactor.finishMemory,finishSegments,ProcActualSegments.build,bind_assoc]
  rfl
end ZkFormal.NearV3.Candidates.ProcActualSegmentFactor
