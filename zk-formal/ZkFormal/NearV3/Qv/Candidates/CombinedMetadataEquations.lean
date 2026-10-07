import ZkFormal.NearV3.Qv.Candidates.CombinedTermination

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec
open CombinedTable

def metadataConstraints : List Expr :=
  [Expr.mul (c lastMain) (Dsl.not (c main)),
   Expr.mul (c lastMain) (Dsl.not (c hi)),
   Expr.mul (c main) (c ValueTable.tau),
   mul3 (c walk) (Dsl.not (c main)) (c lo),
   mul3 (c walk) (Dsl.not (c main)) (c hi),
   mul3 (c walk) (Dsl.not (c main)) (c slot)]


theorem metadata_constraint_mem : ∀ e ∈ metadataConstraints, e ∈ CombinedTable.constraints := by
  intro e he
  simp only [metadataConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [CombinedTable.constraints]

theorem plan_metadata_equations {F : Type} [Lean.Grind.CommRing F]
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    ∀ e ∈ metadataConstraints, e.eval tr t r pub=0 := by
  by_cases ht : w.tau=0
  · cases hl : w.lastMain
    · simp [metadataConstraints,c,k,sub,mul3,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,
        main,lastMain,walk,lo,hi,slot,ValueTable.tau,hl,ht,
        Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
        Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
        Lean.Grind.AddCommGroup.add_neg_cancel]
    · have hh := (plan_last_metadata pre v pres resolve w hw hl).2.2.1
      simp [metadataConstraints,c,k,sub,mul3,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,
        main,lastMain,walk,lo,hi,slot,ValueTable.tau,hl,ht,hh,
        Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
        Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
        Lean.Grind.AddCommGroup.add_neg_cancel]
  · obtain ⟨hk,hs,hl⟩ := plan_implicit_metadata pre v pres resolve w hw ht
    simp [metadataConstraints,c,k,sub,mul3,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,
      main,lastMain,walk,lo,hi,slot,ValueTable.tau,hl,ht,hk,hs,Kind.code,Bool.toNat,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.AddCommGroup.add_neg_cancel]


private theorem nat_sub_cast {F : Type} [Lean.Grind.CommRing F] (a b : Nat) (h : b≤a) :
    (@Nat.cast F Lean.Grind.Semiring.natCast (a-b)) =
      (@Nat.cast F Lean.Grind.Semiring.natCast a) + -(@Nat.cast F Lean.Grind.Semiring.natCast b) := by
  have he := @Lean.Grind.Semiring.natCast_add F _ (a-b) b
  rw [Nat.sub_add_cancel h] at he
  grind

theorem plan_last_count_equation {F : Type} [Lean.Grind.CommRing F]
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    (eqG (c lastMain) (c ValueTable.count) (Expr.mul (c lo) (sub (c slot) (k 2)))).eval
      tr t r pub=0 := by
  cases hl : w.lastMain
  · simp [eqG,c,Expr.eval,Expr.evalWith,rowEnv,hc,lastMain,hl,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.zero_mul]
  · obtain ⟨_,hs,_,hcount⟩ := plan_last_metadata pre v pres resolve w hw hl
    have hsub := nat_sub_cast (F:=F) w.slot 2 hs
    simp [eqG,c,k,sub,Expr.eval,Expr.evalWith,rowEnv,hc,lastMain,ValueTable.count,lo,slot,
      hl,hcount,Lean.Grind.Semiring.natCast_one,Lean.Grind.Semiring.natCast_mul,hsub,
      Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]


theorem plan_end_main_equation {F : Type} [Lean.Grind.CommRing F]
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    (mul3 (c wend) (c main) (Dsl.not (c lastMain))).eval tr t r pub=0 := by
  cases hf : w.final
  · simp [mul3,c,Expr.eval,Expr.evalWith,rowEnv,hc,wend,hf,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.zero_mul]
  · have hm := (plan_final_metadata pre v pres resolve w hw hf).2
    by_cases ht : w.tau=0
    · have hl := hm ht
      simp [mul3,c,k,sub,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,lastMain,hl,
        Lean.Grind.Semiring.natCast_one,Lean.Grind.AddCommGroup.add_neg_cancel,
        Lean.Grind.Semiring.mul_zero]
    · simp [mul3,c,Expr.eval,Expr.evalWith,rowEnv,hc,main,ht,Bool.toNat,
        Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.zero_mul]

theorem plan_absent_buffer_equation {F : Type} [Lean.Grind.CommRing F]
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) (hv : v.Valid)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    (mul3 (c wl) (Expr.mul (c main) (Expr.mul (c lo) (Dsl.not (c hi))))
      (Expr.mul (c absent) (c ValueTable.count))).eval tr t r pub=0 := by
  cases ha : w.value.isSome
  · have hz : w.kind.code=1 → w.count=0 :=
      fun hk => plan_absent_buffer_count pre v pres resolve hv w hw hk ha
    cases hk : w.kind
    all_goals simp [hk,Kind.code] at hz
    all_goals simp_all [mul3,c,k,sub,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,
      lo,hi,Kind.code,ValueTable.count,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
      Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.AddCommGroup.add_neg_cancel]
  · simp [mul3,c,Expr.eval,Expr.evalWith,rowEnv,hc,absent,ha,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen


