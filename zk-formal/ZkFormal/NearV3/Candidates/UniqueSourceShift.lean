import ZkFormal.NearV3.Candidates.UniqueSourceLocal
namespace ZkFormal.NearV3.Candidates.UniqueSourceShift
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates Render.SrcpGen UniqueSourceEquations
theorem step_integer (bs : List SrcpB) (rep : Nat→Bool) (off r H : Nat) (hr : r<H)
    (pub : Nat→Int) :
    ev (UniqueSourceEquations.cellsI bs rep (off+r)) (UniqueSourceEquations.cellsI bs rep (off+((r+1)%H)))
      (if r=0 then 1 else 0) (if r+1=H then 1 else 0)
      (if r+1=H then 0 else 1) pub UniqueSourceCharge.step=0 := by
  by_cases hl : r+1=H
  · simp [UniqueSourceCharge.step,ev,hl]
  · have hm : (r+1)%H=r+1 := Nat.mod_eq_of_lt (by omega)
    have hh:=congrArg (fun n : Nat=>(n : Int)) (UniqueSourceBoundary.step bs (off+r))
    rw [Int.natCast_add,UniqueSourceIncrement.cells bs rep (off+r+1)] at hh
    simp only [Nat.add_assoc] at hh
    simp only [UniqueSourceCharge.step,Dsl.sub,Dsl.n,Dsl.c,Dsl.sum,Dsl.smul,Dsl.mul3,Dsl.not,
      Dsl.k,List.foldl,ev,hl,ite_false,hm,Nat.add_assoc,Int.one_mul]
    simp only [UniqueSourceEquations.cellsI,UniqueSourceRender.cell,ite_true] at *
    simp only [SrcpV3.sz,show (54=54) from rfl,ite_true] at *
    simp only [Bool.false_eq_true,ite_false,←Int.sub_eq_add_neg,show ((44:Nat):Int)=44 from rfl,show ((1:Nat):Int)=1 from rfl,show ((33:Nat):Int)=33 from rfl,Int.mul_assoc] at *
    omega

theorem step_field {tr : Trace Fp} {bs : List SrcpB} {rep : Nat→Bool} {off tt r : Nat}
    {pub : List Fp} (hr : r<tr.height tt)
    (hc : ∀r,r<tr.height tt→∀x,tr.cell tt r x=Fp.ofNat (UniqueSourceRender.cell bs rep (off+r) x)) :
    UniqueSourceCharge.step.eval tr tt r pub=0 := by
  apply eval_zero_of_ev (C:=UniqueSourceEquations.cellsI bs rep (off+r))
    (D:=UniqueSourceEquations.cellsI bs rep (off+((r+1)%tr.height tt)))
    (fun x=>(hc r hr x).trans (ofNat_int _))
    (fun x=>(hc _ (Nat.mod_lt _ (Nat.two_pow_pos _)) x).trans (ofNat_int _))
  exact step_integer bs rep off r (tr.height tt) hr _

end ZkFormal.NearV3.Candidates.UniqueSourceShift
