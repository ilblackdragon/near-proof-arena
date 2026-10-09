import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordTwoRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.Chacha.Table.E ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecSideZero

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8) (hn : R.n≤64) (ht : R.tau<P)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈zeroTests,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,har,ha,hR,hH,hZ,hA,hFA,hgval,hig,he7,hkval,hNN,hik,hekl,hhp,hsj,htau,hit,hzt⟩ :=
    ProcPriorCodecRecordZeroRows.actual I R present gb fwd vidV k f gg s out hf hg h
  obtain ⟨b,hbr,hi2,he2⟩ := ProcPriorCodecRecordTwoRows.actual I R present gb fwd vidV k f gg s out hk hf hg h
  have hab : b=a := Array.push_inj_right.mp (hbr.symm.trans har)
  subst b
  have hgP : gg<P := Nat.lt_trans hg (by decide +kernel)
  have hN : R.n*R.n≤4096 := Nat.mul_le_mul hn hn
  have hkP : k<P := by
    have hh : 4096<P := by decide +kernel
    omega
  have hnP : R.n*R.n-1<P := by
    have hh : 4096<P := by decide +kernel
    omega
  have hpos : 1≤R.n*R.n := by omega
  have hNcast : Fp.ofNat (R.n*R.n-1)=Fp.ofNat (R.n*R.n)-1 := by
    have hNat : R.n*R.n-1+1=R.n*R.n := by omega
    have hh := congrArg Fp.ofNat hNat
    rw [ProcPriorCodecEndArithmetic.cast_add] at hh
    change Fp.ofNat (R.n*R.n-1)+(1:Fp)=Fp.ofNat (R.n*R.n) at hh
    grind only
  refine ⟨a,har,?_⟩
  simp only [zeroTests,recordTests,List.forall_mem_append]
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · apply difference _ nxt first last trans _ _ ig7 e7 gg 7 hgP (by decide +kernel)
    · change Fp.ofNat a[kR]! =1; rw [hR]; rfl
    · change Fp.ofNat a[Codec.g]! + -(Fp.ofNat 7)=_
      rw [hgval,Lean.Grind.Ring.sub_eq_add_neg]
    · rw [hig]
    · rw [he7]; split <;> rfl
  · by_cases hfa : f=2
    · apply difference _ nxt first last trans _ _ ig2 e2 gg 2 hgP (by decide +kernel)
      · change Fp.ofNat a[fA]! =1; rw [hFA,if_pos hfa]; rfl
      · change Fp.ofNat a[Codec.g]! + -(Fp.ofNat 2)=_
        rw [hgval,Lean.Grind.Ring.sub_eq_add_neg]
      · rw [hi2 hfa]
      · rw [he2]; by_cases hh:gg=2 <;> simp only [hfa,hh,and_self,ite_true,ite_false] <;> rfl
    · apply disabled
      · change Fp.ofNat a[fA]! =0; rw [hFA,if_neg hfa]; rfl
      · change Fp.ofNat a[e2]! =0; rw [he2,if_neg (by simp [hfa])]; rfl
  · apply difference _ nxt first last trans _ _ ikl ekl k (R.n*R.n-1) hkP hnP
    · change Fp.ofNat a[kR]! =1; rw [hR]; rfl
    · change Fp.ofNat a[kidx]! + -(Fp.ofNat a[NN]! + -(Fp.ofNat 1))=_
      rw [hkval,hNN,hNcast]
      change Fp.ofNat k + -(Fp.ofNat (R.n*R.n)+ -(1:Fp))=_
      grind only
    · rw [hik]
    · rw [hekl]
      have hh : k+1=R.n*R.n ↔ k=R.n*R.n-1 := by omega
      simp only [hh]; split <;> rfl
  · apply disabled
    · change Fp.ofNat a[kH]! =0; rw [hH]; rfl
    · change Fp.ofNat a[ehp]! =0; rw [hhp]; rfl
  · apply disabled
    · change Fp.ofNat a[kZ]! +Fp.ofNat a[kA]! =0; rw [hZ,hA]; decide +kernel
    · change Fp.ofNat a[esj]! =0; rw [hsj]; rfl
  · exact tau_test a R.tau ht nxt first last trans ha htau hit hzt
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroLocal
