import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordStep
import ZkFormal.NearV3.Candidates.ProcActualParameterGuard
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceGuard
open NearSpecV3 NearSpecV3.Scheduler
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- The corrected record's split prior value and comparison bit implement
saturation of the full original allowance, including its high bytes. -/
theorem split_saturation (a fair : Nat) :
    (if (if a≥16777216 then 1 else 0)=1 then Codec.MA else
      if (if Codec.MA≤a%16777216+fair then 1 else 0)=1 then Codec.MA
      else a%16777216+fair) = min (a+fair) Codec.MA := by
  by_cases ha : a≥16777216
  · have hm : Codec.MA≤a+fair := by change 4500000≤a+fair; omega
    simp [ha,Nat.min_eq_right hm]
  · have hmod : a%16777216=a := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    by_cases hm : Codec.MA≤a+fair
    · simp [ha,hm,Nat.min_eq_right hm]
    · simp [ha,hm,Nat.min_eq_left (by omega : a+fair≤Codec.MA)]

/-- Boolean grid allowance and link-pass branching use identical subtraction. -/
theorem allowed_subtraction (a base : Nat) (allowed : Bool) :
    a-b2n allowed*base = (if allowed then a-base else a) := by
  cases allowed <;> simp [b2n]

/-- A current-layout link reads the original prior allowance lookup, not a
canonicalized prior state's positional array. -/
theorem link_cell (I : Input) (k : Nat) (hk : k<I.ids.length*I.ids.length)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p) :
    (linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).a2[k]! =
      min ((ProcActualInput.allowances I.ids I.prev)[k]!+I.p.maxShardBandwidth/I.ids.length) Codec.MA
        -b2n I.allowed[k]!*I.p.base := by
  have hm : I.p.maxAllowance=Codec.MA := by rw [lp_calc hp]; rfl
  simp only [linkPass]
  rw [getElem!_pos _ k (by simpa using hk)]
  simp only [Array.getElem_map,List.getElem_toArray,List.getElem_range]
  rw [hm,allowed_subtraction]

theorem record_allowance (I : Input) (R : Run) (present : Bool) (k cb : Nat)
    (hn : R.n=I.ids.length) (hk : k<R.n*R.n)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (ha : R.a2=(linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).a2)
    (hz : present=false → (ProcActualInput.allowances I.ids I.prev)[k]! = 0)
    (hc : cb=(if Codec.MA≤(if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0)%16777216+
      I.p.maxShardBandwidth/R.n then 1 else 0)) :
    let a := if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0
    (if (if a≥16777216 then 1 else 0)=1 then Codec.MA else
      if cb=1 then Codec.MA else a%16777216+I.p.maxShardBandwidth/R.n)
      -b2n I.allowed[k]!*I.p.base = R.a2[k]! := by
  dsimp only
  rw [hc,split_saturation,ha,link_cell I k (by simpa [hn] using hk) hp,hn]
  cases present with
  | true => rfl
  | false => simp [hz rfl]

theorem record_check (I : Input) (R : Run) (present : Bool) (k cb : Nat)
    (hn : R.n=I.ids.length) (hk : k<R.n*R.n)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p)
    (ha : R.a2=(linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)).a2)
    (hz : present=false → (ProcActualInput.allowances I.ids I.prev)[k]! = 0)
    (hc : cb=(if Codec.MA≤(if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0)%16777216+
      I.p.maxShardBandwidth/R.n then 1 else 0)) :
    let a := if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0
    Gen.check (((if (if a≥16777216 then 1 else 0)=1 then Codec.MA else
      if cb=1 then Codec.MA else a%16777216+I.p.maxShardBandwidth/R.n)
      -b2n I.allowed[k]!*I.p.base) == R.a2[k]!) "codec a2 differs from the link pass"=.ok () := by
  have he := record_allowance I R present k cb hn hk hp ha hz hc
  dsimp only at *
  rw [he]
  simp [Gen.check,pure,Except.pure]

end ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceGuard
