import ZkFormal.NearV3.Candidates.PairPackingStudy
import ZkFormal.NearV3.Candidates.ShaPackingTrace

namespace ZkFormal.NearV3.Candidates.ShaPartialBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Table.E
open PairPackingStudy (shaPairs before)
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def expr := PairPackingStudy.expression shaPairs

def pairE (p : Nat) : Expr :=
  if p∈shaPairs then .col (p-before shaPairs p) false
  else .add (PairPackingStudy.column shaPairs p false)
    (smul 2 (PairPackingStudy.column shaPairs (p+1) false))

def byteE (start : Nat) : Expr :=
  sum ((List.range 4).map fun j => smul (4^j) (pairE (start+2*j)))

/-- Closed syntax check of the selected non-overlapping adjacent data pairs. -/
theorem pair_syntax : ∀p:Fin 192, 2*p.val∈shaPairs →
    PairPackingStudy.column shaPairs (2*p.val) false=
      ShaCarryPairs.low (.col (2*p.val-before shaPairs (2*p.val)) false) ∧
    PairPackingStudy.column shaPairs (2*p.val+1) false=
      ShaCarryPairs.high (.col (2*p.val-before shaPairs (2*p.val)) false) := by
  decide +kernel

/-- Polynomial cancellation is valid for every field value, not only range4. -/
theorem low_high (x : Fp) : ShaCarryPairs.decodeLow x+2*ShaCarryPairs.decodeHigh x=x := by
  simp only [ShaCarryPairs.decodeLow,ShaCarryPairs.decodeHigh,ShaCarryPairs.low,
    ShaCarryPairs.high,Expr.evalWith,ShaCarryPairs.scalarEnv,smul,sub,k]
  have hp : (2013265921:Fp)=0 := by decide +kernel
  grind

theorem pair_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (p : Fin 192) :
    (expr (.col (2*p.val) false)).eval tr t r pub +
      2*(expr (.col (2*p.val+1) false)).eval tr t r pub =
    (pairE (2*p.val)).eval tr t r pub := by
  change (PairPackingStudy.column shaPairs (2*p.val) false).eval tr t r pub +
    2*(PairPackingStudy.column shaPairs (2*p.val+1) false).eval tr t r pub = _
  by_cases hp : 2*p.val∈shaPairs
  · rw [(pair_syntax p hp).1,(pair_syntax p hp).2]
    simp only [pairE,if_pos hp]
    exact low_high _
  · simp only [pairE,if_neg hp,Expr.eval,Expr.evalWith,smul,rowEnv]
    rfl

theorem byte_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (q : Fin 48) :
    (expr (bits (fun i => Expr.col i false) (8*q.val) 8)).eval tr t r pub =
      (byteE (8*q.val)).eval tr t r pub := by
  have hq := q.isLt
  have hp (j : Nat) (hj : j<4) :
      (expr (.col (8*q.val+2*j) false)).eval tr t r pub +
        2*(expr (.col (8*q.val+2*j+1) false)).eval tr t r pub =
      (pairE (8*q.val+2*j)).eval tr t r pub := by
    have h := pair_eval tr t r pub ⟨4*q.val+j,by omega⟩
    simpa only [Nat.mul_add,show 2*(4*q.val)=8*q.val by omega] using h
  have h0:=hp 0 (by decide)
  have h1:=hp 1 (by decide)
  have h2:=hp 2 (by decide)
  have h3:=hp 3 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.reduceMul] at h0 h1 h2 h3
  simp only [byteE,bits,List.range_succ,List.range_zero,List.map_append,List.map_cons,
    List.map_nil,List.nil_append,List.cons_append,sum,smul,expr,PairPackingStudy.expression,Expr.eval,Expr.evalWith,
    rowEnv,Nat.reducePow,Nat.reduceMul,Nat.add_zero]
  simp only [expr,Expr.eval,PairPackingStudy.expression,rowEnv,Nat.add_assoc,Nat.reduceAdd] at h0 h1 h2 h3
  grind

end ZkFormal.NearV3.Candidates.ShaPartialBytes
