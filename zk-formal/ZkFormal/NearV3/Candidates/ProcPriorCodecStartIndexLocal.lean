import ZkFormal.NearV3.Candidates.ProcPriorCodecStartIndexData
import ZkFormal.NearV3.Candidates.ProcPriorCodecStartZeroRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecStartIndexLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecSideZero
open ZkFormal.Chacha.Table.E

def equations : List Expr := ProcPriorCodecActual.additions.take 8

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : State)
    (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) (hn:R.n≤64)
    (h:step I R present gb fwd (instanceCells I R present vidV) k f g s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈equations,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨a,ha,hsrc,huse,hhas,hrs,hnn,hidx,hehp⟩ :=
    ProcPriorCodecStartIndexData.actual I R present gb fwd vidV k f g s out hf hg h
  obtain ⟨b,hb,hstart,hoff⟩ := ProcPriorCodecStartZeroRows.actual I R present gb fwd vidV k f g s out hk hf hg h
  have heq:b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  have hn0 : 0<R.n := Nat.pos_of_ne_zero (by intro he; simp [he] at hk)
  have hnp : R.n<P := Nat.lt_of_le_of_lt hn (by decide +kernel)
  have hup : k%R.n<P := Nat.lt_trans (Nat.mod_lt _ hn0) hnp
  have hnm : R.n-1<P := by omega
  have hnc : Fp.ofNat (R.n-1)=Fp.ofNat R.n-1 := by
    have he : R.n-1+1=R.n := by omega
    have hh:=congrArg Fp.ofNat he
    rw [ProcPriorCodecEndArithmetic.cast_add] at hh
    change Fp.ofNat (R.n-1)+(1:Fp)=Fp.ofNat R.n at hh
    grind only
  have hindex : Fp.ofNat a[kidx]! =Fp.ofNat a[srcC]!*Fp.ofNat a[nn]!+Fp.ofNat a[useC]! := by
    rw [hidx,hsrc,huse,hnn,←ProcPriorCodecEndArithmetic.cast_mul,←ProcPriorCodecEndArithmetic.cast_add]
    congr 1
    simpa only [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div k R.n).symm
  refine ⟨a,ha,?_⟩
  by_cases hs:f=0 ∧ g=0
  · obtain ⟨hnzb,hig2,hib⟩:=hstart hs
    have hrs1:a[rs]! =1 := by simpa only [if_pos hs] using hrs
    have hw : ∀e∈isZ (c rs) (sub (c useC) (sub (c nn) (ZkFormal.Chacha.Table.E.k 1))) ib hasC,
        e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
      apply difference _ nxt first last trans _ _ ib hasC (k%R.n) (R.n-1) hup hnm
      · change Fp.ofNat a[rs]! =1; rw [hrs1]; rfl
      · change Fp.ofNat a[useC]! + -(Fp.ofNat a[nn]! + -(Fp.ofNat 1))=_
        rw [huse,hnn,hnc]; change Fp.ofNat (k%R.n)+ -(Fp.ofNat R.n+ -(1:Fp))=_; grind only
      · rw [hib]
      · rw [hhas]
        have he : k%R.n+1=R.n ↔ k%R.n=R.n-1 := by omega
        simp only [he]; split <;> rfl
    have hz : ∀e∈isZ (c rs) (c useC) ig2 nzb,
        e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
      apply enabled _ nxt first last trans _ _ ig2 nzb (k%R.n)
      · change Fp.ofNat a[rs]! =1; rw [hrs1]; rfl
      · change Fp.ofNat a[useC]! =Fp.ofNat (k%R.n); rw [huse]
      · rw [hig2]
      · rw [hnzb,Nat.mod_eq_of_lt hup]; split <;> rfl
    intro e he
    simp only [equations,ProcPriorCodecActual.additions,isZ,List.take_succ_cons,List.take_zero,
      List.cons_append,List.nil_append,List.mem_cons,List.mem_nil_iff,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change Fp.ofNat a[ehp]!*nxt srcC=0; rw [hehp]; change (0:Fp)*_=0; grind only
    · change Fp.ofNat a[ehp]!*nxt useC=0; rw [hehp]; change (0:Fp)*_=0; grind only
    · change Fp.ofNat a[rs]!*(Fp.ofNat a[kidx]! + -(Fp.ofNat a[srcC]!*Fp.ofNat a[nn]!+Fp.ofNat a[useC]!))=0
      rw [hindex]; grind only
    · exact hw _ (by simp [isZ])
    · exact hw _ (by simp [isZ])
    · exact hz _ (by simp [isZ])
    · exact hz _ (by simp [isZ])
    · simp only [mul3,notE,sub,c,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
        Bool.false_eq_true,ite_false,hrs1,show Fp.ofNat 1=(1:Fp) from rfl]
      grind only
  · have hrs0:a[rs]! =0 := by simpa only [if_neg hs] using hrs
    have hz:=hoff hs
    simp only [equations,ProcPriorCodecActual.additions,isZ,List.take_succ_cons,List.take_zero,
      List.cons_append,List.nil_append,List.forall_mem_cons,List.forall_mem_nil]
    simp only [mul3,notE,sub,c,n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
      Bool.false_eq_true,ite_false,ite_true,hrs0,hz,hehp,show Fp.ofNat 0=(0:Fp) from rfl]
    simp only [List.not_mem_nil,false_implies,forall_const]
    grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecStartIndexLocal
