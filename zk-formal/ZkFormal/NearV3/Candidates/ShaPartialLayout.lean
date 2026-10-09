import ZkFormal.NearV3.Candidates.PairPackingStudy

namespace ZkFormal.NearV3.Candidates.ShaPartialLayout
open ZkFormal.Air

def digit (i b : Nat) (nx : Bool) : Expr :=
  if b%2=0 then ShaCarryPairs.low (.col i nx) else ShaCarryPairs.high (.col i nx)

def column (i : Nat) (nx : Bool) : Expr :=
  if i<128 then
    let j:=i/32
    let b:=i%32
    if j%2=0 then
      if b<16 then digit (24*j+b/2) b nx else .col (24*j+b-8) nx
    else
      if b<16 then .col (24*j+b) nx else digit (24*j+16+(b-16)/2) b nx
  else if i<384 then
    let j:=(i-128)/32
    let b:=(i-128)%32
    if b<18 then digit (96+23*j+b/2) b nx else .col (96+23*j+b-9) nx
  else .col (i-104) nx

def expression : Expr → Expr
  | .col i nx => column i nx
  | .add a b => .add (expression a) (expression b)
  | .mul a b => .mul (expression a) (expression b)
  | .neg a => .neg (expression a)
  | e => e

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
theorem column_eq : ∀i:Fin 520,∀nx:Bool,column i.val nx=
    PairPackingStudy.column PairPackingStudy.shaPairs i.val nx := by decide +kernel

theorem expression_eq (e : Expr) (h : e.colBound≤520) : expression e=
    PairPackingStudy.expression PairPackingStudy.shaPairs e := by
  induction e with
  | col i nx => exact column_eq ⟨i,by change i+1≤520 at h; omega⟩ nx
  | add a b ia ib =>
    simp only [Expr.colBound] at h
    simp only [expression,PairPackingStudy.expression,ia (by omega),ib (by omega)]
  | mul a b ia ib =>
    simp only [Expr.colBound] at h
    simp only [expression,PairPackingStudy.expression,ia (by omega),ib (by omega)]
  | neg a ia => exact congrArg Expr.neg (ia h)
  | _ => rfl
end ZkFormal.NearV3.Candidates.ShaPartialLayout
