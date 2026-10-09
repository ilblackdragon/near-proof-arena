import ZkFormal.NearV3.Candidates.ProcRecordConcatBoundary
import ZkFormal.NearV3.Candidates.ProcRecordConcatCells
namespace ZkFormal.NearV3.Candidates.ProcRecordBlockLocal
open NearSpec NearSpec.Bandwidth ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched
open ProcPriorCells ProcPriorRecordTrace

def finish (tau : Nat) (next : Option (List Nat)) : Nat→Fp :=
  match next with
  | none=>fun _=>0
  | some ids=>ProcPriorRecordCells.header ids (tau+1)
def after (ids : List Nat) (tau : Nat) (rs : List LinkAllowance)
    (next : Option (List Nat)) (p : Nat) : Nat→Fp :=
  if p<1+9*rs.length then cells ids tau rs p else finish tau next

theorem constraints (ids : List Nat) (tau : Nat) (rs : List LinkAllowance)
    (hr:∀r∈rs,LinkOk r) (p : Nat) (hp:p<1+9*rs.length) (fi : Fp)
    (hf:fi=0 ∨ tau=0) (next : Option (List Nat)) (e : Expr)
    (he:e∈ProcPriorRecordTable.constraints) :
    e.evalWith (env (cells ids tau rs p) (after ids tau rs next (p+1))
      (if p=0 then fi else 0) 0 1)=0 := by
  by_cases h0:p=0
  · subst p
    rw [header]
    simp only [ite_true]
    cases hfirst:rs[0]? with
    | none =>
      have hn:rs.length=0:=by have hh:=List.getElem?_eq_none_iff.mp hfirst; omega
      simp only [after,hn,Nat.mul_zero,Nat.add_zero,show ¬1<1 by omega,ite_false]
      cases next with
      | none => exact ProcPriorRecordEmpty.empty_constraints ids tau fi hf e he
      | some ns => exact ProcRecordConcatBoundary.empty_header ids ns tau fi hf e he
    | some r =>
      have hn:0<rs.length:=(List.getElem?_eq_some_iff.mp hfirst).1
      rw [after,if_pos (by omega : 0+1<1+9*rs.length)]
      have hs:=active ids tau rs 0 0 0 r hfirst (by omega) (by omega)
      change cells ids tau rs 1=_ at hs
      rw [hs]
      exact ProcPriorRecordHeader.start_constraints ids tau r fi hf e he
  · rw [if_neg h0]
    let j:=(p-1)/9
    let w:=((p-1)%9)/3
    let g:=(p-1)%3
    have hj:j<rs.length:=by dsimp [j]; omega
    have hw:w<3:=by dsimp [w]; omega
    have hg:g<3:=by dsimp [g]; omega
    have hplace:p=place j w g:=by dsimp [j,w,g,place]; omega
    clear_value j w g
    let r:=rs[j]
    have hget:rs[j]?=some r:=List.getElem?_eq_getElem hj
    have hv:=ProcPriorRecordConstraints.value_bound r (hr r (List.getElem_mem hj)) j w g hw
    rw [hplace,active ids tau rs j w g r hget hw hg]
    by_cases hend:g=2
    · subst g
      by_cases hwEnd:w=2
      · subst w
        have hnext:place j 2 2+1=place (j+1) 0 0:=by unfold place; omega
        rw [hnext]
        cases hn:rs[j+1]? with
        | none =>
          have hlen:rs.length≤j+1:=List.getElem?_eq_none_iff.mp hn
          rw [after,if_neg (by unfold place; omega : ¬place (j+1) 0 0<1+9*rs.length)]
          cases next with
          | none => exact ProcPriorRecordEnd.end_constraints ids tau j r hv e he
          | some ns => exact ProcRecordConcatBoundary.end_header ids ns tau j r hv e he
        | some s =>
          have hlen:j+1<rs.length:=(List.getElem?_eq_some_iff.mp hn).1
          rw [after,if_pos (by unfold place; omega : place (j+1) 0 0<1+9*rs.length),
            active ids tau rs (j+1) 0 0 s hn (by omega) (by omega)]
          exact ProcPriorRecordNext.next_constraints ids tau j r s hv e he
      · have hnext:place j w 2+1=place j (w+1) 0:=by unfold place; omega
        rw [hnext,after,if_pos (by unfold place; omega : place j (w+1) 0<1+9*rs.length),
          active ids tau rs j (w+1) 0 r hget (by omega) (by omega)]
        exact ProcPriorRecordWordEnd.end_constraints ids tau j w r (by omega) hv e he
    · have hnext:place j w g+1=place j w (g+1):=by unfold place; omega
      rw [hnext,after,if_pos (by unfold place; omega : place j w (g+1)<1+9*rs.length),
        active ids tau rs j w (g+1) r hget hw (by omega)]
      exact ProcPriorRecordInner.inner_constraints ids tau j w g r hw (by omega) hv e he
end ZkFormal.NearV3.Candidates.ProcRecordBlockLocal
