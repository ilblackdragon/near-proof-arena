import ZkFormal.NearV3.Qv.Candidates.CombinedMainSteps

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
open CombinedTable
variable {F : Type} [Lean.Grind.CommRing F]

def stepConstraints : List Expr := mainStepConstraints ++
  [eqG leaveMain (n main) (k 0),eqG leaveMain (n ValueTable.tau) (k 1),
   eqG advanceImplicit (n main) (k 0),
   eqG advanceImplicit (n ValueTable.tau) (Expr.add (c ValueTable.tau) (k 1))]

private theorem eqG_zero (tr : Trace F) (t r : Nat) (pub : List F) (g a b : Expr)
    (hg : g.eval tr t r pub=0) : (eqG g a b).eval tr t r pub=0 := by
  change g.eval tr t r pub * (a.eval tr t r pub + -b.eval tr t r pub)=0
  rw [hg,Lean.Grind.Semiring.zero_mul]

theorem Walk.closed_step_constraints (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (he : pos+1≠w.kind.bytes.length ∨ w.final=true) :
    ∀ e ∈ stepConstraints, e.eval tr t r pub=0 := by
  have hg : ∀ e ∈ [more,advanceMain,leaveMain,advanceImplicit],e.eval tr t r pub=0 := by
    rcases he with hp | hf
    · exact w.nonterminal_step_gates pos b tr t r pub hc hp
    · exact w.final_step_gates pos b tr t r pub hc hf
  have hm := hg advanceMain (by simp)
  have hl := hg leaveMain (by simp)
  have hi := hg advanceImplicit (by simp)
  simp [stepConstraints,mainStepConstraints,eqG_zero tr t r pub _ _ _ hm,
    eqG_zero tr t r pub _ _ _ hl,eqG_zero tr t r pub _ _ _ hi]

theorem main_step_other_gates (w : Walk) (ht : w.tau=0) (hl : w.lastMain=false)
    (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    leaveMain.eval tr t r pub=0 ∧ advanceImplicit.eval tr t r pub=0 := by
  simp [leaveMain,advanceImplicit,c,k,sub,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,
    main,lastMain,ht,hl,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

theorem enter_step_other_gates (w : Walk) (ht : w.tau=0) (hl : w.lastMain=true)
    (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    advanceMain.eval tr t r pub=0 ∧ advanceImplicit.eval tr t r pub=0 := by
  simp [advanceMain,advanceImplicit,mul3,c,k,sub,Dsl.not,Expr.eval,Expr.evalWith,rowEnv,hc,
    main,lastMain,ht,hl,Lean.Grind.Semiring.natCast_one,
    Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

theorem implicit_step_other_gates (w : Walk) (ht : w.tau≠0) (hl : w.lastMain=false)
    (pos : Nat) (b : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0)) :
    advanceMain.eval tr t r pub=0 ∧ leaveMain.eval tr t r pub=0 := by
  simp [advanceMain,leaveMain,mul3,c,Expr.eval,Expr.evalWith,rowEnv,hc,main,lastMain,ht,hl,
    Bool.toNat,Lean.Grind.Semiring.natCast_zero,
    Lean.Grind.Semiring.mul_zero,Lean.Grind.Semiring.zero_mul]


theorem main_step_all (a b : Walk) (i count : Nat)
    (ha : a.orderData=(0,i,count,min i 3))
    (hb : b.orderData=(0,i+1,count,min (i+1) 3)) (hl : a.lastMain=false)
    (pos : Nat) (ab bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((a.row pos ab).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((b.row 0 bb).getD c 0)) :
    ∀ e ∈ stepConstraints,e.eval tr t r pub=0 := by
  have ht : a.tau=0 := congrArg Prod.fst ha
  have hg := main_step_other_gates a ht hl pos ab tr t r pub hc
  intro e he
  rcases List.mem_append.mp he with hm | hi
  · exact main_step_equations a b i count ha hb pos ab bb tr t r pub hc hn e hm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals first | exact eqG_zero tr t r pub _ _ _ hg.1 | exact eqG_zero tr t r pub _ _ _ hg.2

theorem enter_step_all (a b : Walk) (ht : a.tau=0) (hl : a.lastMain=true) (hb : b.tau=1)
    (pos : Nat) (ab bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((a.row pos ab).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((b.row 0 bb).getD c 0)) :
    ∀ e ∈ stepConstraints,e.eval tr t r pub=0 := by
  have hg := enter_step_other_gates a ht hl pos ab tr t r pub hc
  have he := enter_implicit_equations b hb bb tr t r pub hn
  simp only [stepConstraints,List.forall_mem_append]
  constructor
  · simp [mainStepConstraints,eqG_zero tr t r pub _ _ _ hg.1]
  · simp only [List.forall_mem_cons,List.forall_mem_nil,and_true]
    exact ⟨he _ (by simp),he _ (by simp),eqG_zero tr t r pub _ _ _ hg.2,
      eqG_zero tr t r pub _ _ _ hg.2,by simp⟩

theorem implicit_step_all (a b : Walk) (ht : a.tau≠0) (hl : a.lastMain=false)
    (hb : b.tau=a.tau+1)
    (pos : Nat) (ab bb : UInt8) (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((a.row pos ab).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((b.row 0 bb).getD c 0)) :
    ∀ e ∈ stepConstraints,e.eval tr t r pub=0 := by
  have hg := implicit_step_other_gates a ht hl pos ab tr t r pub hc
  have he := implicit_step_equations a b hb pos ab bb tr t r pub hc hn
  simp only [stepConstraints,List.forall_mem_append]
  constructor
  · simp [mainStepConstraints,eqG_zero tr t r pub _ _ _ hg.1]
  · simp only [List.forall_mem_cons,List.forall_mem_nil,and_true]
    exact ⟨eqG_zero tr t r pub _ _ _ hg.2,eqG_zero tr t r pub _ _ _ hg.2,
      he _ (by simp),he _ (by simp),by simp⟩

theorem step_mem : ∀ e ∈ stepConstraints, e ∈ CombinedTable.constraints := by
  intro e he
  rcases List.mem_append.mp he with hm | hi
  · exact main_step_mem e hm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals simp [CombinedTable.constraints]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen

