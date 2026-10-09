import ZkFormal.NearV3.Rcpt.Candidates.DedupInactiveRetarget

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

theorem rowEnv_cellEnv (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowEnv tr tt r pub = cellEnv (tr.cell tt r) (tr.cell tt ((r+1)%tr.height tt))
      (if r=0 then 1 else 0) (if r+1=tr.height tt then 1 else 0)
      (if r+1=tr.height tt then 0 else 1) (fun i => pub.getD i 0) := by
  unfold rowEnv cellEnv
  congr 1
  funext x nx
  cases nx <;> rfl

/-- Only cells below an expression's declared width can affect its value. This
lets the authenticated57-field carry tuple identify the overlap for constraints. -/
theorem cellEnv_congr (ex : Expr) {W : Nat} (hW : ex.colBound ≤ W)
    {C D C' D' : Nat → Fp} (hC : ∀ x, x<W → C x=C' x) (hD : ∀ x, x<W → D x=D' x)
    (fst lst trn : Fp) (pub : Nat → Fp) :
    ex.evalWith (cellEnv C D fst lst trn pub) =
    ex.evalWith (cellEnv C' D' fst lst trn pub) := by
  induction ex with
  | col x nx =>
    have hx : x<W := by simp only [Expr.colBound] at hW; omega
    cases nx <;> simp only [Expr.evalWith, cellEnv, Bool.false_eq_true, ite_false, ite_true]
    · exact hC x hx
    · exact hD x hx
  | add a b ha hb | mul a b ha hb =>
    have hh : a.colBound ≤ W ∧ b.colBound ≤ W := by
      simpa only [Expr.colBound, Nat.max_le] using hW
    simp only [Expr.evalWith]
    rw [ha hh.1, hb hh.2]; rfl
  | neg a ha => exact congrArg (fun x : Fp => -x) (ha hW)
  | _ => rfl

set_option maxRecDepth 32768 in
theorem base_constraint_width : ∀ ex ∈ DedupTable.constraints, ex.colBound ≤ 57 := by
  have hh : DedupTable.constraints.all (fun e => decide (e.colBound ≤ 57)) = true := by
    decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp hh e he)

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
