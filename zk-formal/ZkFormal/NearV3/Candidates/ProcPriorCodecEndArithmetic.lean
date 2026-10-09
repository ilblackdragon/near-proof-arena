import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceGuard
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTotal
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

def credited (I : Input) (R : Run) (present : Bool) (k carry : Nat) : Nat :=
  let a := if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0
  if 16777216≤a then Codec.MA else if carry=1 then Codec.MA else a%16777216+I.p.maxShardBandwidth/R.n

/-- Native PV86 parameters ensure the base debit cannot truncate the natural
subtraction, regardless of the decoded prior allowance or carry value. -/
theorem debit_le (I : Input) (R : Run) (present : Bool) (k carry : Nat)
    (hn : R.n=I.ids.length) (hn1 : 1≤I.ids.length)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p) :
    b2n I.allowed[k]!*I.p.base≤credited I R present k carry := by
  obtain ⟨_,_,_,_,_,hfair⟩ := pv86_facts hn1 hp
  have hbase := (pv86_base_le hp).1
  have hm : I.p.base≤Codec.MA := by change I.p.base≤4500000; omega
  have hc : I.p.base≤credited I R present k carry := by
    dsimp only [credited]
    generalize (if present then (ProcActualInput.allowances I.ids I.prev)[k]! else 0)=a
    rw [hn]
    split
    · exact hm
    · split
      · exact hm
      · omega
  cases he : I.allowed[k]! <;> simpa [b2n,he] using (show (if I.allowed[k]! then I.p.base else 0)≤credited I R present k carry by split <;> omega)

theorem cast_add (a b : Nat) : Fp.ofNat (a+b)=Fp.ofNat a+Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat,Fp.add_def,Fp.toNat_add]
  exact Nat.add_mod _ _ _
theorem cast_mul (a b : Nat) : Fp.ofNat (a*b)=Fp.ofNat a*Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat,Fp.mul_def,Fp.toNat_mul]
  exact Nat.mul_mod _ _ _
theorem debit_field (I : Input) (R : Run) (present : Bool) (k carry : Nat)
    (hn : R.n=I.ids.length) (hn1 : 1≤I.ids.length)
    (hp : Params.calculate Config.pv86 I.ids.length=some I.p) :
    Fp.ofNat (ProcPriorCodecRecordTotal.endAllowance I R present k carry)=
      Fp.ofNat (credited I R present k carry)-Fp.ofNat (b2n I.allowed[k]!)*Fp.ofNat I.p.base := by
  have h := congrArg Fp.ofNat (Nat.sub_add_cancel (debit_le I R present k carry hn hn1 hp))
  rw [cast_add,cast_mul] at h
  change Fp.ofNat (credited I R present k carry-b2n I.allowed[k]!*I.p.base)=_
  grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
