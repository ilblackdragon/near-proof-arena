import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryBit
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordFair
import ZkFormal.NearV3.Candidates.ProcPriorCodecCarryRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecEndSaturation
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecEndArithmetic

theorem saturation_field (v fair carry : Nat) (hc : carry≤1) :
    Fp.ofNat (if 16777216≤v then 4500000 else if carry=1 then 4500000 else v%16777216+fair)=
      (4500000:Fp)*Fp.ofNat (if 16777216≤v then 1 else 0)+
      (1-Fp.ofNat (if 16777216≤v then 1 else 0))*
        ((4500000:Fp)*Fp.ofNat carry+(1-Fp.ofNat carry)*(Fp.ofNat (v%16777216)+Fp.ofNat fair)) := by
  have hh : carry=0 ∨ carry=1 := by omega
  rcases hh with rfl|rfl
  all_goals by_cases hv : 16777216≤v
  all_goals simp only [hv,ite_true,ite_false,show (0:Nat)≠1 by decide,
    cast_add,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl,
    show Fp.ofNat 4500000=(4500000:Fp) from rfl]
  all_goals grind only

theorem constraint (cur nxt : Nat→Fp) (first last trans : Fp)
    (hcredit : cur a1=(4500000:Fp)*cur bigR+(1-cur bigR)*
      ((4500000:Fp)*cur cb+(1-cur cb)*(cur apR+cur fair))) :
    ∀e∈(cRec.drop 55).take 1,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  subst e
  simp only [notE,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env]
  simp only [Bool.false_eq_true,ite_false,Codec.MA,show Fp.ofNat 1=(1:Fp) from rfl,show Fp.ofNat 4500000=(4500000:Fp) from rfl]
  simp only [Lean.Grind.AddCommGroup.sub_eq_add_neg] at hcredit
  rw [hcredit,Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k : Nat) (rows : Array (Array Nat))
    (cmps : List (Nat×Nat×Nat)) (mid out : State) (hk : k<R.n*R.n)
    (hp : forIn (List.range 7) (rows,cmps,0,0,0,0)
      (fun g s=>step I R present gb fwd (instanceCells I R present vidV) k 2 g s)=.ok mid)
    (ht : step I R present gb fwd (instanceCells I R present vidV) k 2 7 mid=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=mid.1.push a ∧ ∀e∈(cRec.drop 55).take 1,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  have hbit : mid.2.2.2.2.2≤1 := ProcPriorCodecCarryBit.bytes I R present gb fwd
    (instanceCells I R present vidV) k (List.range 7) (rows,cmps,0,0,0,0) mid
    (by intro g hg; simp at hg; omega) (by simp) hp
  obtain ⟨a,har,ha1,_⟩ := ProcPriorCodecEndRows.cells I R present gb fwd vidV k mid out hk ht
  obtain ⟨a',ha'r,hap,hbig,hcb⟩ := ProcPriorCodecCarryRows.cells I R present gb fwd
    (instanceCells I R present vidV) k 7 mid out (by decide) hk (by decide) ht
  have he : a'=a := Array.push_inj_right.mp (ha'r.symm.trans har)
  subst a'
  obtain ⟨a',ha'r,hfair⟩ := ProcPriorCodecRecordFair.actual I R present gb fwd vidV k 2 7 mid out (by decide) (by decide) ht
  have he : a'=a := Array.push_inj_right.mp (ha'r.symm.trans har)
  subst a'
  have hc : out.2.2.2.2.2=mid.2.2.2.2.2 := by
    simpa using ProcPriorCodecCarryTotal.byte_carry I R present gb fwd (instanceCells I R present vidV) k 7 mid out (by decide) ht
  have hcredit : Fp.ofNat a[a1]! =
      (4500000:Fp)*Fp.ofNat a[bigR]! +(1-Fp.ofNat a[bigR]!)*
        ((4500000:Fp)*Fp.ofNat a[cb]! +(1-Fp.ofNat a[cb]!)*(Fp.ofNat a[apR]!+Fp.ofNat a[fair]!)) := by
    rw [ha1,hbig,hcb,hc,hap,hfair]
    dsimp only [credited]
    exact saturation_field _ _ _ hbit
  exact ⟨a,har,constraint _ nxt first last trans hcredit⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecEndSaturation
