import ZkFormal.NearV3.Qv.Candidates.CombinedStepCases

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl
open CombinedTable
variable {F : Type} [Lean.Grind.CommRing F]

def insideConstraints : List Expr :=
  [eqG inside (n walk) (k 1),Expr.mul inside (n wf),
   eqG inside (n wp) (Expr.add (c wp) (k 1))] ++
  [lo,hi,slot,ValueTable.vid,ValueTable.tau,ValueTable.users,absent,main,lastMain,ValueTable.count].map
    (fun x => eqG inside (n x) (c x))

def startConstraints : List Expr := [eqG more (n walk) (k 1),eqG more (n wf) (k 1)]

theorem Walk.inside_constraints (w : Walk) (pos : Nat) (b nb : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row (pos+1) nb).getD c 0)) :
    ∀ e ∈ insideConstraints,e.eval tr t r pub=0 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact w.inside_clock pos b nb tr t r pub hc hn e he
  · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    exact w.inside_metadata pos b nb tr t r pub hc hn x hx

theorem Walk.terminal_inside_zero (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0))
    (hp : pos+1=w.kind.bytes.length) : inside.eval tr t r pub=0 := by
  simp [inside,c,Dsl.not,k,sub,Expr.eval,Expr.evalWith,rowEnv,hc,wl,hp,
    Lean.Grind.Semiring.natCast_one,Lean.Grind.AddCommGroup.add_neg_cancel,
    Lean.Grind.Semiring.mul_zero]

theorem inside_constraints_zero (tr : Trace F) (t r : Nat) (pub : List F)
    (hg : inside.eval tr t r pub=0) :
    ∀ e ∈ insideConstraints,e.eval tr t r pub=0 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    all_goals
      change inside.eval tr t r pub * _ = 0
      rw [hg,Lean.Grind.Semiring.zero_mul]
  · obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
    change inside.eval tr t r pub * _ = 0
    rw [hg,Lean.Grind.Semiring.zero_mul]

theorem start_constraints_zero (tr : Trace F) (t r : Nat) (pub : List F)
    (hg : more.eval tr t r pub=0) :
    ∀ e ∈ startConstraints,e.eval tr t r pub=0 := by
  intro e he
  simp only [startConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl
  all_goals
    change more.eval tr t r pub * _ = 0
    rw [hg,Lean.Grind.Semiring.zero_mul]

theorem Walk.internal_neighbor_constraints (w : Walk) (pos : Nat) (b nb : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row (pos+1) nb).getD c 0)) (hp : pos+1≠w.kind.bytes.length) :
    ∀ e ∈ insideConstraints ++ startConstraints ++ stepConstraints,e.eval tr t r pub=0 := by
  have hg := w.nonterminal_step_gates pos b tr t r pub hc hp more (by simp)
  simp only [List.forall_mem_append]
  exact ⟨⟨w.inside_constraints pos b nb tr t r pub hc hn,
    start_constraints_zero tr t r pub hg⟩,w.closed_step_constraints pos b tr t r pub hc (Or.inl hp)⟩

theorem Walk.final_neighbor_constraints (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0))
    (hp : pos+1=w.kind.bytes.length) (hf : w.final=true) :
    ∀ e ∈ insideConstraints ++ startConstraints ++ stepConstraints,e.eval tr t r pub=0 := by
  have hi := w.terminal_inside_zero pos b tr t r pub hc hp
  have hg := w.final_step_gates pos b tr t r pub hc hf more (by simp)
  simp only [List.forall_mem_append]
  exact ⟨⟨inside_constraints_zero tr t r pub hi,start_constraints_zero tr t r pub hg⟩,
    w.closed_step_constraints pos b tr t r pub hc (Or.inr hf)⟩

theorem Walk.terminal_clock_constraints (w next : Walk) (pos : Nat) (b nb : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0))
    (hn : ∀ c, tr.cell t ((r+1)%tr.height t) c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((next.row 0 nb).getD c 0)) (hp : pos+1=w.kind.bytes.length) :
    ∀ e ∈ insideConstraints ++ startConstraints,e.eval tr t r pub=0 := by
  simp only [List.forall_mem_append]
  exact ⟨inside_constraints_zero tr t r pub (w.terminal_inside_zero pos b tr t r pub hc hp),
    next_word_start_equations next nb tr t r pub hn⟩

theorem neighbor_constraints_mem :
    ∀ e ∈ insideConstraints ++ startConstraints ++ stepConstraints,
      e ∈ CombinedTable.constraints := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl | rfl
        all_goals simp [CombinedTable.constraints]
      · apply List.mem_append_right
        exact he
    · simp only [startConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl
      all_goals simp [CombinedTable.constraints]
  · exact step_mem e he

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
