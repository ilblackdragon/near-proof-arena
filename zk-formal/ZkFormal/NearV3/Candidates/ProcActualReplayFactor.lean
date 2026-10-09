import ZkFormal.NearV3.Candidates.ProcActualRoundFactor
import ZkFormal.NearV3.Candidates.ProcActualFinalStateGuards
namespace ZkFormal.NearV3.Candidates.ProcActualReplayFactor
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound

def readStep (aa gg : Array Nat) (c : CReq) (ops : Array (Array Gen.MOp)) :
    Except String (ForInStep (Array (Array Gen.MOp))) :=
  .ok (.yield (ops.modify c.link (·.push
    ⟨c.cid+1,OP_READ,aa[c.link]!,aa[c.link]!,gg[c.link]!,gg[c.link]!,0,false,false,false⟩)))

def replay (I : Input) (cv : Array CReq) (rs : List Round) : Except String Acc := do
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  let ops ← forIn cv (Array.replicate (I.ids.length*I.ids.length) #[]) (readStep lp.a2 lp.g2)
  forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords I.seed))

def finish (I : Input) (tau : Nat) (conv : Array CReq) (stF : PState) (acc : Acc) : Except String Run := do
  let n := I.ids.length
  let p := I.p
  let N := n*n
  let lp := linkPass n p I.allowed (ProcActualInput.allowances I.ids I.prev)
  let al (l : Nat) : Bool := I.allowed[l]!
  let key := NearSpecV3.leWords I.seed
  let (sb,rb,aa,gg,opsL,opsS,opsR,pushes,bucketsAll,_,kpos,_,_,used,rounds,_) := acc
  -- every push is popped exactly once
  check (sortPush pushes.toList == sortPush bucketsAll.toList) "push log ≠ buckets"
  -- final state
  check (sb == stF.sb && rb == stF.rb && aa == stF.al && gg == stF.g) "final state differs"
  check (kpos == rngPos stF.rng) "final RNG position differs"
  -- memory segments
  let mut segs : Array Gen.Seg := #[]
  for l in List.range N do
    let b := al l
    segs := segs.push ⟨addrOf tau 0 l, true, b, b2n b, lp.a2[l]!, lp.g2[l]!, opsL[l]!.toList⟩
  for s in List.range n do
    segs := segs.push ⟨addrOf tau 1 s, false, false, 0, lp.sb[s]!, 0, opsS[s]!.toList⟩
  for r in List.range n do
    segs := segs.push ⟨addrOf tau 2 r, false, false, 0, lp.rb[r]!, 0, opsR[r]!.toList⟩
  -- comparator messages
  let cmpOf (x y : Nat) : Nat × Nat × Nat := (x, y, if y ≤ x then 1 else 0)
  let mut cmps : Array (Nat × Nat × Nat) := #[]
  for g in segs do
    let mut tp := 0
    for o in g.ops do
      check (tp < o.t) "memory times not increasing"
      cmps := cmps.push (cmpOf o.t (tp + 1))
      if o.op == OP_GRANT then cmps := cmps.push (cmpOf o.vin o.inc)
      tp := o.t
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

theorem rest_eq (I : Input) (tau : Nat) (cv : Array CReq) (st : PState) (rs : List Round) :
    ProcActualRoundFactor.runRestRounds I tau cv st rs =
      (replay I cv rs >>= finish I tau cv st) := by
  simp only [ProcActualRoundFactor.runRestRounds,replay,
    ProcActualReplayInitial.initial,bind_assoc]
  rfl
end ZkFormal.NearV3.Candidates.ProcActualReplayFactor
