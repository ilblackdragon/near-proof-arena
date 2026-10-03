import NpaiIR.Basic

/-! # Compiler correctness: `exec` on placed code = `run`, then continue -/

namespace NpaiIR

open ArenaCore Interp

variable {σ : Type} {p : Program} {inp : Inputs} {H : HashOracle σ}

/-- The compiled code of `st` (placed at `b`) is in `p`. -/
def Placed (p : Program) (b : Nat) (st : Stmt) : Prop :=
  ∀ i, i < st.size → p.code[b + i]? = (st.compile b)[i]?

theorem placed_seq {b : Nat} {x y : Stmt} (h : Placed p b (.seq x y)) :
    Placed p b x ∧ Placed p (b + x.size) y := by
  constructor
  · intro i hi
    have := h i (by simp [Stmt.size]; omega)
    rw [this]; simp only [Stmt.compile]
    rw [List.getElem?_append_left (by rw [Stmt.compile_length]; exact hi)]
  · intro i hi
    have := h (x.size + i) (by simp [Stmt.size]; omega)
    rw [← Nat.add_assoc] at this
    rw [this]; simp only [Stmt.compile]
    rw [List.getElem?_append_right (by rw [Stmt.compile_length]; omega), Stmt.compile_length]
    simp

theorem placed_ite {b r : Nat} {t e : Stmt} (h : Placed p b (.ite r t e)) :
    p.code[b]? = some (.jz r (b + t.size + 2)) ∧ Placed p (b + 1) t ∧
    p.code[b + 1 + t.size]? = some (.jmp (b + t.size + 2 + e.size)) ∧
    Placed p (b + t.size + 2) e := by
  have hl := Stmt.compile_length t (b + 1)
  have hl2 := Stmt.compile_length e (b + t.size + 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h 0 (by simp [Stmt.size]); simpa [Stmt.compile] using this
  · intro i hi
    have := h (1 + i) (by simp [Stmt.size]; omega)
    rw [show b + (1 + i) = b + 1 + i by omega] at this
    rw [this]; simp only [Stmt.compile, List.append_assoc]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp [hl]; omega)]
    simp
  · have := h (1 + t.size) (by simp [Stmt.size]; omega)
    rw [show b + (1 + t.size) = b + 1 + t.size by omega] at this
    rw [this]; simp only [Stmt.compile, List.append_assoc]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp [hl])]
    simp [hl]
  · intro i hi
    have := h (t.size + 2 + i) (by simp [Stmt.size]; omega)
    rw [show b + (t.size + 2 + i) = b + t.size + 2 + i by omega] at this
    rw [this]; simp only [Stmt.compile, List.append_assoc]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp [hl]; omega),
      List.getElem?_append_right (by simp [hl]; omega)]
    simp [hl]; congr 1; omega

theorem placed_loop {b r : Nat} {body : Stmt} (h : Placed p b (.loop r body)) :
    p.code[b]? = some (.jz r (b + body.size + 2)) ∧ Placed p (b + 1) body ∧
    p.code[b + 1 + body.size]? = some (.jmp b) := by
  have hl := Stmt.compile_length body (b + 1)
  refine ⟨?_, ?_, ?_⟩
  · have := h 0 (by simp [Stmt.size]); simpa [Stmt.compile] using this
  · intro i hi
    have := h (1 + i) (by simp [Stmt.size]; omega)
    rw [show b + (1 + i) = b + 1 + i by omega] at this
    rw [this]; simp only [Stmt.compile, List.append_assoc]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp [hl]; omega)]
    simp
  · have := h (1 + body.size) (by simp [Stmt.size]; omega)
    rw [show b + (1 + body.size) = b + 1 + body.size by omega] at this
    rw [this]; simp only [Stmt.compile, List.append_assoc]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp [hl])]
    simp [hl]

/-! ## One-instruction facts -/

theorem stepI_jz (r t : Nat) (s : State σ) :
    stepI p inp H (.jz r t) s =
      bif Nat.blt s.fuel 1 then .done .outOfFuel s
      else .next { s with fuel := s.fuel - 1, pc := bif Nat.beq (s.regs r) 0 then t else s.pc + 1 } := by
  simp [stepI, cost, exec1]

theorem stepI_jmp (t : Nat) (s : State σ) :
    stepI p inp H (.jmp t) s =
      bif Nat.blt s.fuel 1 then .done .outOfFuel s
      else .next { s with fuel := s.fuel - 1, pc := t } := by
  simp [stepI, cost, exec1]

theorem stepI_halt_ne_next (r : Nat) (s s' : State σ) :
    stepI p inp H (.halt r) s ≠ .next s' := by
  simp only [stepI, cost, exec1]
  cases Nat.blt s.fuel 1 <;> simp

theorem stepI_plain_pc {i : Instr} (hi : plain i = true) {s s' : State σ}
    (h : stepI p inp H i s = .next s') : s'.pc = s.pc + 1 := by
  cases i <;> simp only [plain] at hi <;>
    simp only [stepI, exec1, Bool.cond_eq_ite] at h <;>
    (repeat' split at h) <;>
    first
    | (cases h; rfl)
    | (injection h with h; subst h; rfl)
    | simp_all

/-! ## The simulation -/

/-- What the machine does after the fragment's run. -/
def after (p : Program) (inp : Inputs) (H : HashOracle σ) : Res σ → Outcome × State σ
  | .cont s' g' => exec p inp H g' s'
  | .stop o s' => (o, s')

def EndsAt (r : Res σ) (e : Nat) : Prop :=
  ∀ s' g', r = .cont s' g' → s'.pc = e

theorem exec_zero (s : State σ) : exec p inp H 0 s = (.outOfFuel, s) := rfl

theorem exec_succ' (g : Nat) (s : State σ) :
    exec p inp H (g + 1) s = match step p inp H s with
      | .next s' => exec p inp H g s'
      | .done o s' => (o, s') := rfl

theorem fetch0 {b : Nat} {st : Stmt} (h : Placed p b st) (hs : 0 < st.size) :
    p.code[b]? = (st.compile b)[0]? := by simpa using h 0 hs

/-- **Compiler correctness.** Running the machine on placed code equals
running the structured program and then continuing the machine; a normal
exit leaves `pc` just past the fragment. -/
theorem exec_placed : ∀ (st : Stmt), st.wf → ∀ (g : Nat) (s : State σ), Placed p s.pc st →
    exec p inp H g s = after p inp H (run p inp H g st s).1 ∧
      EndsAt (run p inp H g st s).1 (s.pc + st.size)
  | st, _, 0, s, _ => by
    cases st <;> simp [run.eq_1, after, EndsAt, exec_zero]
  | .op i, hw, g + 1, s, hp => by
    have hf : p.code[s.pc]? = some i := by simpa [Stmt.compile] using fetch0 hp (by simp [Stmt.size])
    rw [exec_succ', step_of_fetch hf, run.eq_2]
    cases hs : stepI p inp H i s with
    | next s' =>
      refine ⟨rfl, ?_⟩
      intro s'' g' he; cases he
      simpa [Stmt.size] using stepI_plain_pc hw hs
    | done o s' => exact ⟨rfl, fun _ _ he => by cases he⟩
  | .halt r, _, g + 1, s, hp => by
    have hf : p.code[s.pc]? = some (.halt r) := by simpa [Stmt.compile] using fetch0 hp (by simp [Stmt.size])
    rw [exec_succ', step_of_fetch hf, run.eq_3]
    cases hs : stepI p inp H (.halt r) s with
    | next s' => exact absurd hs (stepI_halt_ne_next r s s')
    | done o s' => exact ⟨rfl, fun _ _ he => by cases he⟩
  | .seq a b, hw, g + 1, s, hp => by
    obtain ⟨hpa, hpb⟩ := placed_seq hp
    obtain ⟨ea, pa⟩ := exec_placed a hw.1 (g + 1) s hpa
    rw [run.eq_4]
    rcases hr : run p inp H (g + 1) a s with ⟨r, hr'⟩
    rw [hr] at ea pa
    cases r with
    | stop o s' => exact ⟨ea, fun _ _ he => by cases he⟩
    | cont s' g' =>
      have hpc : s'.pc = s.pc + a.size := pa s' g' rfl
      have hg' : g' ≤ g + 1 := by simpa [Res.gas] using hr'
      rw [← hpc] at hpb
      obtain ⟨eb, pb⟩ := exec_placed b hw.2 g' s' hpb
      refine ⟨ea.trans eb, ?_⟩
      intro s'' g'' he
      rw [pb s'' g'' he, hpc]; simp [Stmt.size]; omega
  | .ite r t e, hw, g + 1, s, hp => by
    obtain ⟨hjz, hpt, hjmp, hpe⟩ := placed_ite hp
    rw [exec_succ', step_of_fetch hjz, run.eq_5, stepI_jz]
    cases hb : Nat.blt s.fuel 1
    · simp only [Bool.cond_false]
      by_cases hz : s.regs r = 0
      · have hbe : Nat.beq (s.regs r) 0 = true := nbeq_true hz
        simp only [hz, ↓reduceIte, hbe, Bool.cond_true]
        obtain ⟨ee, pe⟩ := exec_placed e hw.2 g { s with fuel := s.fuel - 1, pc := s.pc + t.size + 2 } hpe
        refine ⟨ee, ?_⟩
        intro s' g' he; rw [pe s' g' he]; simp [Stmt.size]; omega
      · have hbe : Nat.beq (s.regs r) 0 = false := nbeq_false hz
        simp only [hz, ↓reduceIte, hbe, Bool.cond_false]
        obtain ⟨et, pt⟩ := exec_placed t hw.1 g { s with fuel := s.fuel - 1, pc := s.pc + 1 } hpt
        rw [et]
        rcases hr : run p inp H g t { s with fuel := s.fuel - 1, pc := s.pc + 1 } with ⟨x, hx⟩
        rw [hr] at pt
        cases x with
        | stop o s' => exact ⟨rfl, fun _ _ he => by cases he⟩
        | cont s2 g2 =>
          have hpc : s2.pc = s.pc + 1 + t.size := by simpa using pt s2 g2 rfl
          cases g2 with
          | zero => exact ⟨rfl, fun _ _ he => by cases he⟩
          | succ g3 =>
            simp only [after]
            rw [exec_succ', step_of_fetch (by rw [hpc]; exact hjmp), stepI_jmp]
            cases hb2 : Nat.blt s2.fuel 1
            · refine ⟨rfl, ?_⟩
              intro s' g' he; cases he; simp [Stmt.size]; omega
            · exact ⟨rfl, fun _ _ he => by cases he⟩
    · simp only [Bool.cond_true]
      exact ⟨rfl, fun _ _ he => by cases he⟩
  | .loop r body, hw, g + 1, s, hp => by
    obtain ⟨hjz, hpb, hjmp⟩ := placed_loop hp
    rw [exec_succ', step_of_fetch hjz, run.eq_6, stepI_jz]
    cases hb : Nat.blt s.fuel 1
    · simp only [Bool.cond_false]
      by_cases hz : s.regs r = 0
      · have hbe : Nat.beq (s.regs r) 0 = true := nbeq_true hz
        simp only [hz, ↓reduceIte, hbe, Bool.cond_true]
        refine ⟨rfl, ?_⟩
        intro s' g' he; cases he; simp [Stmt.size]; omega
      · have hbe : Nat.beq (s.regs r) 0 = false := nbeq_false hz
        simp only [hz, ↓reduceIte, hbe, Bool.cond_false]
        obtain ⟨eb, pb⟩ := exec_placed body hw g { s with fuel := s.fuel - 1, pc := s.pc + 1 } hpb
        rw [eb]
        rcases hr : run p inp H g body { s with fuel := s.fuel - 1, pc := s.pc + 1 } with ⟨x, hx⟩
        rw [hr] at pb
        cases x with
        | stop o s' => exact ⟨rfl, fun _ _ he => by cases he⟩
        | cont s2 g2 =>
          have hpc : s2.pc = s.pc + 1 + body.size := by simpa using pb s2 g2 rfl
          cases g2 with
          | zero => exact ⟨rfl, fun _ _ he => by cases he⟩
          | succ g3 =>
            simp only [after]
            rw [exec_succ', step_of_fetch (by rw [hpc]; exact hjmp), stepI_jmp]
            cases hb2 : Nat.blt s2.fuel 1
            · simp only [Bool.cond_false]
              have hx3 : g3 < g + 1 := by simp [Res.gas] at hx; omega
              exact exec_placed (.loop r body) hw g3 { s2 with fuel := s2.fuel - 1, pc := s.pc } (by simpa using hp)
            · exact ⟨rfl, fun _ _ he => by cases he⟩
    · simp only [Bool.cond_true]
      exact ⟨rfl, fun _ _ he => by cases he⟩
termination_by st _ g => (g, sizeOf st)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp; omega)
    | (apply Prod.Lex.left; omega)
    | (apply lex_le_lt <;> simp_all [Res.gas] <;> omega)

end NpaiIR

namespace NpaiIR

open ArenaCore Interp

variable {σ : Type}

/-- Whole-program form: a program whose code is exactly `st.compile 0`
behaves, from the initial state, as `run` followed by the machine (which
traps if `st` falls off the end). -/
theorem exec_program (prog : Program) (st : Stmt) (hw : st.wf) (hcode : prog.code = st.compile 0)
    (inp : Inputs) (H : HashOracle σ) (g fuel : Nat) (hs : σ) :
    exec prog inp H g (init prog fuel hs) = after prog inp H (run prog inp H g st (init prog fuel hs)).1 := by
  refine (exec_placed st hw g _ ?_).1
  intro i _
  simp [init, hcode]

end NpaiIR
