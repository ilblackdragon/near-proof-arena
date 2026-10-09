import ZkFormal.NearV3.Candidates.ProcPriorCodecGridStride
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridRecords
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
/-- Every record is forced by corrected constraints, not by a generated-row premise. -/
theorem records (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1) (hk:cv tr t r kidx=0)
    (hN:cv tr t r NN≤4096) :
    ∀k,k<cv tr t r NN→r+24*k<tr.height t ∧ cv tr t (r+24*k) rs=1 ∧
      cv tr t (r+24*k) kidx=k ∧
      ∀x∈[tau,pres,vid,nn,NN,base,fair],cv tr t (r+24*k) x=cv tr t r x := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.mul_zero,Nat.add_zero]
    exact ⟨hr,hs,hk,by simp⟩
  | succ k ih =>
    intro hkn
    obtain ⟨hb,hsb,hkb,hcb⟩:=ih (by omega)
    have hn:=hcb NN (by simp)
    obtain ⟨hb1,hs1,hk1,hc1⟩:=ProcPriorCodecGridStride.next_record hL hb hsb (by omega) (by omega)
    have he:r+24*k+24=r+24*(k+1):=by omega
    rw [he] at hb1 hs1 hk1 hc1
    refine ⟨hb1,hs1,by omega,?_⟩
    intro x hx
    exact (hc1 x hx).trans (hcb x hx)
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridRecords
