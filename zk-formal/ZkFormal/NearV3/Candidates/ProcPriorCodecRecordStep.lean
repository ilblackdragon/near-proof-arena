import ZkFormal.NearV3.Candidates.ProcPriorCodecExtra
import ZkFormal.NearV3.Candidates.ProcPriorCodecAssignments
import ZkFormal.NearV3.Candidates.ProcActualInput
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched.Codec
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
abbrev State := Array (Array Nat) × List (Nat×Nat×Nat) × Nat × Nat × Nat × Nat

def step (I : Input) (R : Run) (present : Bool) (gbA : Array Nat) (fwd : List (Nat×Nat))
    (inst : List (Nat×Nat)) (kk f gg : Nat) (st : State) : Except String (ForInStep State) := do
  let n := R.n
  let N := n*n
  let tv := R.tau
  let fairV := I.p.maxShardBandwidth/n
  let baseV := I.p.base
  let a0 := Array.replicate N 0
  let afinF (k : Nat) := (R.segs.getD k default).vfin
  let gfinF (k : Nat) := (R.segs.getD k default).wfin
  let mut rows := st.1
  let mut cmps := st.2.1
  let mut apv := st.2.2.1
  let mut apostv := st.2.2.2.1
  let mut bigv := st.2.2.2.2.1
  let mut cbv := st.2.2.2.2.2
  let p := 5 + 24 * kk + 8 * f + gg
  let bpo := if f < 2 then idByte I.ids kk (8 * f + gg) else (if gg < 3 then afinF kk / 256 ^ gg % 256 else 0)
  let bpr := if ¬present then 0 else if f < 2 then bpo else a0[kk]! / 256 ^ gg % 256
  let lowfv := if gg < 3 then 1 else 0
  let wtv := 256 ^ gg
  let nzbv := if bpr = 0 then 0 else 1
  let isEnd := f = 2 ∧ gg = 7
  -- link data of record kk (from `SDG`, carried over the record) and its source record
  let sender := kk/n
  let receiver := kk%n
  let wrap := receiver+1=n
  let a0s := if present then (ProcActualInput.allowances I.ids I.prev)[kk]! else 0
  let apRv := a0s % 16777216
  let bigRv := if a0s ≥ 16777216 then 1 else 0
  let alv := b2n (I.allowed[kk]!)
  let gbv := gbA[kk]!
  let mut extra : List (Nat × Nat) := ProcPriorCodecExtra.baseExtra n kk f gg alv gbv
  if f=0 ∧ gg=0 then
    extra := extra ++ ProcPriorCodecExtra.startExtra n kk
  if f = 2 ∧ gg ≥ 2 then extra := extra ++ ProcPriorCodecExtra.priorExtra apRv bigRv
  if f = 2 then
    extra := extra ++ ProcPriorCodecExtra.allowanceExtra gg lowfv wtv apv bigv apostv nzbv bpr
    if gg = 2 then
      extra := extra ++ ProcPriorCodecExtra.wrapExtra n kk
      let x := apRv + fairV
      cbv := if Codec.MA ≤ x then 1 else 0
      cmps := cmps ++ [(x, Codec.MA, cbv)]
      extra := extra ++ ProcPriorCodecExtra.compareExtra x cbv
    if gg ≥ 2 then extra := extra ++ ProcPriorCodecExtra.carryExtra cbv
  if isEnd then
    let bFv := if bigv = 1 ∨ nzbv = 1 then 1 else 0
    let a1v := if bigRv = 1 then Codec.MA else (if cbv = 1 then Codec.MA else apRv + fairV)
    let a2v := a1v - alv * baseV
    ZkFormal.NearV3.Sched.Gen.check (a2v == R.a2[kk]!) "codec a2 differs from the link pass"
    let gf := gfinF kk
    let lastRec := kk + 1 = N
    extra := extra ++ ProcPriorCodecExtra.endExtra bFv a1v a2v alv baseV (afinF kk) gf receiver
    if tv = 0 then
      let ft := ((fwd.find? (·.1 == kk)).map (·.2)).getD 0
      ZkFormal.NearV3.Sched.Gen.check (ft ≤ gf + gbv) "forwarding demand above the grant"
      cmps := cmps ++ [(gf + gbv, ft, 1)]
      extra := extra ++ ProcPriorCodecExtra.forwardExtra gf gbv ft kk
  rows := rows.push (ProcPriorCodecAssignments.recordRow I present n kk f gg p bpo bpr inst extra)
  if f = 2 ∧ gg < 3 then
    apv := apv + wtv * bpr
    apostv := apostv + wtv * bpo
  if f = 2 ∧ gg ≥ 3 ∧ bpr ≠ 0 then bigv := 1
  return .yield (rows,cmps,apv,apostv,bigv,cbv)
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
