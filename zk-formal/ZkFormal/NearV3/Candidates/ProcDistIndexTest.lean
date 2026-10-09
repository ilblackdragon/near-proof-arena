import ZkFormal.NearV3.Candidates.ProcScanRequestArithmetic
namespace ZkFormal.NearV3.Candidates.ProcDistIndexTest
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

theorem inverse (i n:Nat)(hi:i<n)(hn:n≤64) :
    (Fp.ofNat i-(Fp.ofNat n-1))*Fp.ofNat (finv (fsub i (n-1)))=
      1-(if i+1=n then 1 else 0) := by
  have hnp:n-1<P:=by unfold P;omega
  have hip:i<P:=by unfold P;omega
  have hn1:n=1+(n-1):=by omega
  have hf:=congrArg Fp.ofNat hn1
  simp only [←ZkFormal.Near.ofNat_add'] at hf
  have hcast:Fp.ofNat n-1=Fp.ofNat (n-1):=by
    change Fp.ofNat n=(1:Fp)+Fp.ofNat (n-1) at hf
    grind only
  rw [hcast,←SchedField.fsub_cast,SchedField.inverse_product]
  have hz:=ProcKeyInverse.difference_zero i (n-1) hip hnp
  have he:i=n-1↔i+1=n:=by omega
  simp only [hz,he]
  split <;> grind only

theorem annihilate (i n:Nat)(hi:i<n) :
    (Fp.ofNat i-(Fp.ofNat n-1))*(if i+1=n then 1 else 0)=0 := by
  by_cases h:i+1=n
  · have hf:=congrArg Fp.ofNat h
    simp only [←ZkFormal.Near.ofNat_add'] at hf
    change Fp.ofNat i+(1:Fp)=Fp.ofNat n at hf
    rw [if_pos h];grind only
  · rw [if_neg h];grind only
end ZkFormal.NearV3.Candidates.ProcDistIndexTest
