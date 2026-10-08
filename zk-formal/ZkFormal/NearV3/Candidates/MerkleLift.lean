import ZkFormal.NearV3.Candidates.MerkleBranches

namespace ZkFormal.NearV3.Candidates.MerkleEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

/-- Add the nonempty control columns at one physical table, preserving its
original58 columns, all heights, and every other table. -/
def liftTrace (tr : Trace Fp) (tt : Nat) (pub : List Fp) : Trace Fp :=
  {log:=tr.log, cell:=fun t r x =>
    if t=tt then
      if x=emptyCol then 0 else if x=inverseCol then (countE.eval tr tt 0 pub)⁻¹
      else tr.cell t r x
    else tr.cell t r x}

theorem lift_old (tr : Trace Fp) (tt r x : Nat) (pub : List Fp) (hx : x<58) :
    (liftTrace tr tt pub).cell tt r x=tr.cell tt r x := by
  simp [liftTrace,emptyCol,inverseCol,show x≠58 by omega,show x≠59 by omega]

theorem lift_flag (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    (liftTrace tr tt pub).cell tt r emptyCol=0 := by simp [liftTrace]

theorem lift_eval (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (e : Expr)
    (hb : e.colBound≤58) :
    e.eval (liftTrace tr tt pub) tt r pub=e.eval tr tt r pub := by
  induction e with
  | col x nx =>
    have hx : x<58 := by simp only [Expr.colBound] at hb; omega
    cases nx <;> exact lift_old tr tt _ x pub hx
  | add a b ha hb' | mul a b ha hb' =>
    have hh : a.colBound≤58 ∧ b.colBound≤58 := by simpa only [Expr.colBound,Nat.max_le] using hb
    simp only [Expr.eval,Expr.evalWith,rowEnv]
    congr 1
    · exact ha hh.1
    · exact hb' hh.2
  | neg a ha => exact congrArg (fun x : Fp => -x) (ha hb)
  | _ => rfl

set_option maxRecDepth 32768 in
theorem old_column_bounds : ∀ e∈MerklePublic.table.exprs, e.colBound≤58 := by
  have h : MerklePublic.table.exprs.all (fun e => decide (e.colBound≤58))=true := by decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

theorem lift_count (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    countE.eval (liftTrace tr tt pub) tt r pub=countE.eval tr tt 0 pub := by
  rw [lift_eval tr tt r pub countE (by decide +kernel),count_row]

set_option maxRecDepth 8192 in
theorem lift_local {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal MerklePublic.table tr tt pub)
    (hc : countE.eval tr tt 0 pub≠0) :
    TableLocal table (liftTrace tr tt pub) tt pub := by
  have hg : ∀ r e, (gate e).eval (liftTrace tr tt pub) tt r pub=
      e.eval (liftTrace tr tt pub) tt r pub := fun r e => gate_zero (lift_flag tr tt r pub) e
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · simp only [eval_bool,eval_c,lift_flag]; grind
        · simp only [eval_sub,eval_n,eval_c,lift_flag]; grind
        · simp only [eval_mul,eval_c,lift_flag]; grind
        · change (gate (sub (.mul countE (c inverseCol)) (k 1))).eval (liftTrace tr tt pub) tt r pub=0
          rw [hg]
          simp only [eval_sub,eval_mul,eval_c,eval_k,lift_count]
          have hinv : (liftTrace tr tt pub).cell tt r inverseCol=(countE.eval tr tt 0 pub)⁻¹ := by
            simp [liftTrace,emptyCol,inverseCol]
          rw [hinv,Fp.mul_inv_cancel hc]
          grind
      · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
        simp only [eval_mul,eval_c,lift_flag]; grind
    · obtain ⟨e,hf,rfl⟩ := List.mem_map.mp he
      rw [hg,lift_eval tr tt r pub e (old_column_bounds e (List.mem_append_left _ hf))]
      exact h.constr r hr e hf
  · intro r hr i hi e he
    obtain ⟨i,hj,rfl⟩ := List.mem_map.mp hi
    obtain ⟨e,hf,rfl⟩ := List.mem_map.mp he
    have hb := old_column_bounds e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hj,List.mem_append_left _ hf⟩))
    rw [hg,lift_eval tr tt r pub e hb]
    exact h.bits r hr i hj e hf

theorem lift_mult (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (es : List Expr)
    (hb : ∀ e∈es, e.colBound≤58) (k : Nat) :
    Interaction.multNat.go (liftTrace tr tt pub) tt r pub es k=
      Interaction.multNat.go tr tt r pub es k := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [Interaction.multNat.go]
    rw [lift_eval tr tt r pub e (hb e (by simp)),ih (fun e he => hb e (by simp [he]))]

theorem lift_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (b : Nat) (sd : Bool) :
    rowTraffic table.interactions (liftTrace tr tt pub) tt r pub b sd=
      rowTraffic MerklePublic.table.interactions tr tt r pub b sd := by
  rw [row_nonempty (lift_flag tr tt r pub)]
  simp only [rowTraffic]
  apply flatMap_congr'
  intro i hi
  have hm : i.multNat (liftTrace tr tt pub) tt r pub=i.multNat tr tt r pub := by
    apply lift_mult
    intro e he
    exact old_column_bounds e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  have hv : i.msgVal (liftTrace tr tt pub) tt r pub=i.msgVal tr tt r pub := by
    apply List.map_congr_left
    intro e he
    exact lift_eval tr tt r pub e (old_column_bounds e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_right _ he⟩)))
  rw [hm,hv]

theorem lift_traffic (tr : Trace Fp) (tt : Nat) (pub : List Fp) (b : Nat) (sd : Bool) (m : List Fp) :
    tableBusCount table.interactions (liftTrace tr tt pub) tt pub b sd m=
      tableBusCount MerklePublic.table.interactions tr tt pub b sd m := by
  simp only [tableBusCount_eq,lift_row]
  rfl

end ZkFormal.NearV3.Candidates.MerkleEmpty
