import ZkFormal.NearV3.Candidates.UniqueSourceIncrement
import ZkFormal.Near.Render.Proof.NodeEv
namespace ZkFormal.NearV3.Candidates.UniqueSourceEquations
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra
open Rcpt.Candidates Render.SrcpGen

def cellsI (bs : List SrcpB) (rep : Nat→Bool) (r x : Nat) : Int :=
  (UniqueSourceRender.cell bs rep r x : Int)

theorem step_integer (bs : List SrcpB) (rep : Nat→Bool) (r H : Nat) (hr : r<H)
    (pub : Nat→Int) :
    ev (cellsI bs rep r) (cellsI bs rep ((r+1)%H))
      (if r=0 then 1 else 0) (if r+1=H then 1 else 0)
      (if r+1=H then 0 else 1) pub UniqueSourceCharge.step=0 := by
  by_cases hl : r+1=H
  · simp [UniqueSourceCharge.step,ev,hl]
  · have hm : (r+1)%H=r+1 := Nat.mod_eq_of_lt (by omega)
    have hh:=congrArg (fun n : Nat=>(n : Int)) (UniqueSourceBoundary.step bs r)
    rw [Int.natCast_add,UniqueSourceIncrement.cells bs rep (r+1)] at hh
    simp only [UniqueSourceCharge.step,Dsl.sub,Dsl.n,Dsl.c,Dsl.sum,Dsl.smul,Dsl.mul3,Dsl.not,
      Dsl.k,List.foldl,ev,hl,ite_false,hm,Int.one_mul]
    simp only [cellsI,UniqueSourceRender.cell,ite_true] at *
    simp only [SrcpV3.sz,show (54=54) from rfl,ite_true] at *
    simp only [Bool.false_eq_true,ite_false,←Int.sub_eq_add_neg,show ((44:Nat):Int)=44 from rfl,show ((1:Nat):Int)=1 from rfl,show ((33:Nat):Int)=33 from rfl,Int.mul_assoc] at *
    omega

theorem initial_integer {bs : List SrcpB} {rep : Nat→Bool}
    (h : DedupRender.TableFacts bs rep) (r H : Nat) (pub : Nat→Int) :
    ev (cellsI bs rep r) (cellsI bs rep ((r+1)%H))
      (if r=0 then 1 else 0) (if r+1=H then 1 else 0)
      (if r+1=H then 0 else 1) pub UniqueSourceCharge.initial=0 := by
  by_cases h0 : r=0
  · subst r
    have hr : 0<DedupRender.R bs := by have hh:=DedupRender.R_ge_33 h;omega
    simp only [UniqueSourceCharge.initial,Dsl.sub,Dsl.c,Dsl.k,ev,ite_true,Int.one_mul,cellsI]
    simp only [UniqueSourceRender.cell,SrcpV3.sz,SrcpV3.rt,SrcpV3.dup,SrcpV3.L,
      show ¬(0=54) by decide,show ¬(14=54) by decide,show ¬(11=54) by decide,ite_false,ite_true]
    rw [UniqueSourceBoundary.first h]
    simp only [DedupRender.cell,hr,ite_true,show ¬(0=56) by decide,
      show ¬(14=56) by decide,show ¬(11=56) by decide,ite_false,DedupRender.firstAt h,
      DedupRender.rowFrame,DedupRender.frame,h.first_dup,Bool.false_eq_true,ite_false,
      rootFrame,Frame.cell,Bool.toNat_false,Bool.toNat_true]
    omega
  · simp [UniqueSourceCharge.initial,ev,h0]

end ZkFormal.NearV3.Candidates.UniqueSourceEquations
