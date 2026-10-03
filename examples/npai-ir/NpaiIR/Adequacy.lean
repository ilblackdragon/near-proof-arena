import NpaiIR.Sem
import NpaiIR.Correct

/-!
# NpaiIR.Adequacy — `Ev` agrees with the machine

* `run_sound`: whatever the gas-indexed `run` does (normal exit, accept) is
  derivable in `Ev` (no fuel hypothesis needed).
* `run_complete`: an `Ev` derivation of cost `c` is replayed by `run` when the
  state has at least `c` fuel and more than `c` gas.
* `exec_accept_iff`: for a whole program `st` compiled at address 0, the
  machine (`ArenaCore.Interp.exec` with gas `fuel + 1`, as in `runWith`)
  accepts iff `Ev st m₀ (halt true) c` for some `c ≤ fuel`.
-/

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-- Abstract view of a machine state. -/
def absS (s : State Unit) : M := ⟨s.regs, s.mem⟩

theorem okInstr_cost_pos (i : Instr) : 1 ≤ cost r i := by
  cases i <;> simp [cost] <;> omega

theorem exec1_ok {i : Instr} (hi : okInstr i = true) (s : State Unit) :
    exec1 p inp deployedRO s i =
      match ins p inp (absS s) i with
      | some m' => .next { s with pc := s.pc + 1, regs := m'.regs, mem := m'.mem }
      | none => .done .trap s := by
  cases i with
  | halt => simp [okInstr] at hi
  | jmp => simp [okInstr] at hi
  | jz => simp [okInstr] at hi
  | jnz => simp [okInstr] at hi
  | out => simp [okInstr] at hi
  | const a imm => rfl
  | mov a b => rfl
  | bin op a b c => rfl
  | addi a b imm => rfl
  | tlen a t => rfl
  | tload a b t =>
    simp only [exec1, ins, absS]
    by_cases h : s.regs b < (inp.tape t).length
    · simp [h, blt_true h]
    · simp [h, blt_false h]
  | tcopy a b c t =>
    simp only [exec1, ins, absS]
    by_cases h1 : s.regs b + s.regs c ≤ (inp.tape t).length
    · by_cases h2 : s.regs a + s.regs c ≤ p.memSize
      · simp [h1, h2, ble_true h1, ble_true h2]
      · simp [h1, h2, ble_true h1, ble_false h2]
    · simp [h1, ble_false h1]
  | ld8 a b =>
    simp only [exec1, ins, absS]
    by_cases h : s.regs b < p.memSize
    · simp [h, blt_true h]
    · simp [h, blt_false h]
  | st8 a b =>
    simp only [exec1, ins, absS]
    by_cases h : s.regs a < p.memSize
    · simp [h, blt_true h]
    · simp [h, blt_false h]
  | sha256 a b c =>
    simp only [exec1, ins, absS]
    by_cases h1 : s.regs b + s.regs c ≤ p.memSize
    · by_cases h2 : s.regs a + 32 ≤ p.memSize
      · simp [h1, h2, ble_true h1, ble_true h2]
      · simp [h1, h2, ble_true h1, ble_false h2]
    · simp [h1, ble_false h1]
  | rohash a b c =>
    simp only [exec1, ins, absS]
    by_cases h1 : s.regs b + s.regs c ≤ p.memSize
    · by_cases h2 : s.regs a + 32 ≤ p.memSize
      · simp [h1, h2, ble_true h1, ble_true h2, deployedRO]
      · simp [h1, h2, ble_true h1, ble_false h2]
    · simp [h1, ble_false h1]
  | memeq a b c d =>
    simp only [exec1, ins, absS]
    by_cases h1 : s.regs b + s.regs d ≤ p.memSize
    · by_cases h2 : s.regs c + s.regs d ≤ p.memSize
      · simp [h1, h2, ble_true h1, ble_true h2]; rfl
      · simp [h1, h2, ble_true h1, ble_false h2]
    · simp [h1, ble_false h1]

theorem stepI_ok {i : Instr} (hi : okInstr i = true) (s : State Unit) :
    stepI p inp deployedRO i s =
      bif Nat.blt s.fuel (cost s.regs i) then .done .outOfFuel s
      else match ins p inp (absS s) i with
        | some m' => .next { s with fuel := s.fuel - cost s.regs i, pc := s.pc + 1,
                                    regs := m'.regs, mem := m'.mem }
        | none => .done .trap { s with fuel := s.fuel - cost s.regs i } := by
  simp only [stepI]
  cases Nat.blt s.fuel (cost s.regs i)
  · simp only [Bool.cond_false]
    rw [exec1_ok hi]
    rfl
  · rfl

@[simp] theorem absS_regs (s : State Unit) : (absS s).regs = s.regs := rfl
@[simp] theorem absS_mem (s : State Unit) : (absS s).mem = s.mem := rfl

theorem absS_upd (s : State Unit) (m : M) (f pc : Nat) :
    absS { s with fuel := f, pc := pc, regs := m.regs, mem := m.mem } = m := by
  cases m; rfl

/-! ## Machine → `Ev` -/

/-- What `run` results tell about `Ev`. -/
def SoundRes (p : Program) (inp : Inputs) (st : Stmt) (s : State Unit) : Res Unit → Prop
  | .cont s' _ => ∃ c, Ev p inp st (absS s) (.ok (absS s')) c
  | .stop .accept _ => ∃ c, Ev p inp st (absS s) (.halt true) c
  | .stop _ _ => True

theorem run_sound : ∀ (g : Nat) (st : Stmt) (s : State Unit), st.ok →
    SoundRes p inp st s (run p inp deployedRO g st s).1
  | 0, st, s, _ => by cases st <;> simp [run.eq_1, SoundRes]
  | g + 1, .op i, s, hok => by
    rw [run.eq_2]
    rw [stepI_ok hok]
    cases hb : Nat.blt s.fuel (cost s.regs i)
    · simp only [Bool.cond_false]
      cases hm : ins p inp (absS s) i with
      | none => simp [SoundRes]
      | some m' =>
        simp only [SoundRes]
        exact ⟨_, by rw [absS_upd]; exact Ev.op hok hm⟩
    · simp [SoundRes]
  | g + 1, .halt r, s, _ => by
    rw [run.eq_3]
    simp only [stepI, cost, exec1]
    cases hb : Nat.blt s.fuel 1
    · cases hz : Nat.beq (s.regs r) 0
      · simp only [Bool.cond_false, SoundRes]
        refine ⟨1, ?_⟩
        have : (s.regs r != 0) = true := by
          have := nbeq_false_iff.mp hz
          simpa using this
        have h := @Ev.halt p inp r (absS s)
        simp only [absS] at h this ⊢
        rw [this] at h; exact h
      · simp [SoundRes]
    · simp [SoundRes]
  | g + 1, .seq a b, s, hok => by
    rw [run.eq_4]
    have iha := run_sound (g + 1) a s hok.1
    rcases hr : run p inp deployedRO (g + 1) a s with ⟨r, hr'⟩
    rw [hr] at iha
    cases r with
    | stop o s' =>
      simp only
      cases o <;> simp only [SoundRes] at iha ⊢
      obtain ⟨c, hc⟩ := iha
      exact ⟨c, Ev.seqHalt hc⟩
    | cont s' g' =>
      simp only
      have hg' : g' ≤ g + 1 := by simpa [Res.gas] using hr'
      obtain ⟨c1, h1⟩ := iha
      have ihb := run_sound g' b s' hok.2
      revert ihb
      rcases run p inp deployedRO g' b s' with ⟨r2, _⟩
      cases r2 with
      | cont s2 _ =>
        rintro ⟨c2, h2⟩; exact ⟨_, Ev.seqOk h1 h2⟩
      | stop o s2 =>
        cases o <;> simp only [SoundRes] <;> intro ih <;> try trivial
        obtain ⟨c2, h2⟩ := ih; exact ⟨_, Ev.seqOk h1 h2⟩
  | g + 1, .ite r t e, s, hok => by
    rw [run.eq_5, stepI_jz]
    cases hb : Nat.blt s.fuel 1
    · simp only [Bool.cond_false]
      by_cases hz : s.regs r = 0
      · rw [if_pos hz, nbeq_true hz]
        simp only [Bool.cond_true]
        have ihe := run_sound g e { s with fuel := s.fuel - 1, pc := s.pc + t.size + 2 } hok.2
        revert ihe
        rcases run p inp deployedRO g e _ with ⟨r2, _⟩
        cases r2 with
        | cont s2 _ =>
          rintro ⟨c2, h2⟩; exact ⟨_, Ev.iteF hz h2⟩
        | stop o s2 =>
          cases o <;> simp only [SoundRes] <;> intro ih <;> try trivial
          obtain ⟨c2, h2⟩ := ih; exact ⟨_, Ev.iteF hz h2⟩
      · rw [if_neg hz, nbeq_false hz]
        simp only [Bool.cond_false]
        have iht := run_sound g t { s with fuel := s.fuel - 1, pc := s.pc + 1 } hok.1
        revert iht
        rcases run p inp deployedRO g t _ with ⟨r2, hr2⟩
        cases r2 with
        | stop o s2 =>
          cases o <;> simp only [SoundRes] <;> intro ih <;> try trivial
          obtain ⟨c2, h2⟩ := ih; exact ⟨_, Ev.iteTHalt hz h2⟩
        | cont s2 g2 =>
          rintro ⟨c2, h2⟩
          cases g2 with
          | zero => simp [SoundRes]
          | succ g3 =>
            simp only
            rw [stepI_jmp]
            cases Nat.blt s2.fuel 1
            · simp only [Bool.cond_false, SoundRes]; exact ⟨_, Ev.iteTOk hz h2⟩
            · simp [SoundRes]
    · simp [SoundRes]
  | g + 1, .loop r body, s, hok => by
    rw [run.eq_6, stepI_jz]
    cases hb : Nat.blt s.fuel 1
    · simp only [Bool.cond_false]
      by_cases hz : s.regs r = 0
      · rw [if_pos hz]
        exact ⟨_, Ev.loopExit hz⟩
      · rw [if_neg hz, nbeq_false hz]
        simp only [Bool.cond_false]
        have ihb := run_sound g body { s with fuel := s.fuel - 1, pc := s.pc + 1 } hok
        revert ihb
        rcases run p inp deployedRO g body _ with ⟨r2, hr2⟩
        cases r2 with
        | stop o s2 =>
          cases o <;> simp only [SoundRes] <;> intro ih <;> try trivial
          obtain ⟨c2, h2⟩ := ih; exact ⟨_, Ev.loopHalt hz h2⟩
        | cont s2 g2 =>
          rintro ⟨c2, h2⟩
          cases g2 with
          | zero => simp [SoundRes]
          | succ g3 =>
            simp only
            rw [stepI_jmp]
            cases Nat.blt s2.fuel 1
            · simp only [Bool.cond_false]
              have hg : g3 < g + 1 := by simp [Res.gas] at hr2; omega
              have ihl := run_sound g3 (.loop r body) { s2 with fuel := s2.fuel - 1, pc := s.pc } hok
              revert ihl
              rcases run p inp deployedRO g3 (.loop r body) _ with ⟨r3, _⟩
              cases r3 with
              | cont s3 _ =>
                rintro ⟨c3, h3⟩; exact ⟨_, Ev.loopIter hz h2 h3⟩
              | stop o s3 =>
                cases o <;> simp only [SoundRes] <;> intro ih <;> try trivial
                obtain ⟨c3, h3⟩ := ih; exact ⟨_, Ev.loopIter hz h2 h3⟩
            · simp [SoundRes]
    · simp [SoundRes]
termination_by g st => (g, sizeOf st)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp; omega)
    | (apply Prod.Lex.left; omega)
    | (apply lex_le_lt <;> simp_all [Res.gas] <;> omega)

/-! ## `Ev` → machine -/

theorem run_complete {st : Stmt} {m : M} {r : R} {c : Nat} (h : Ev p inp st m r c) (hok : st.ok) :
    ∀ (s : State Unit) (g : Nat), absS s = m → c ≤ s.fuel → c < g →
      (∀ m', r = .ok m' → ∃ s' g', (run p inp deployedRO g st s).1 = .cont s' g' ∧ absS s' = m' ∧
          s'.fuel = s.fuel - c ∧ g - c ≤ g') ∧
      (r = .halt true → ∃ s', (run p inp deployedRO g st s).1 = .stop .accept s') := by
  induction h with
  | @op i m m' hi hm =>
    intro s g hs hc hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    refine ⟨?_, fun h => (by cases h)⟩
    rintro m'' he; cases he
    rw [run.eq_2, stepI_ok hi]
    subst hs
    simp only [absS_regs, absS_mem] at *
    rw [blt_false (by omega)]
    simp only [Bool.cond_false, hm]
    refine ⟨_, _, rfl, absS_upd _ _ _ _, rfl, ?_⟩
    have := okInstr_cost_pos (r := s.regs) i; omega
  | opTrap => intro _ _ _ _ _; exact ⟨fun _ h => (by cases h), fun h => (by cases h)⟩
  | @seqOk a b m m1 r c1 c2 _ _ iha ihb =>
    intro s g hs hc hg
    obtain ⟨s1, g1, e1, a1, f1, l1⟩ := (iha hok.1 s g hs (by omega) (by omega)).1 m1 rfl
    have hb := ihb hok.2 s1 g1 a1 (by omega) (by omega)
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [run.eq_4]
    rcases hr : run p inp deployedRO (g + 1) a s with ⟨x, hx⟩
    rw [hr] at e1; simp only at e1; subst e1
    simp only
    constructor
    · intro m' he
      obtain ⟨s', g', e2, a2, f2, l2⟩ := hb.1 m' he
      exact ⟨s', g', e2, a2, by omega, by omega⟩
    · intro he
      exact hb.2 he
  | seqHalt _ iha =>
    intro s g hs hc hg
    refine ⟨fun _ h => (by cases h), fun he => ?_⟩
    cases he
    obtain ⟨s', e⟩ := (iha hok.1 s g hs hc hg).2 rfl
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [run.eq_4]
    rcases hr : run p inp deployedRO (g + 1) _ s with ⟨x, hx⟩
    rw [hr] at e; simp only at e; subst e
    exact ⟨s', rfl⟩
  | seqTrap => intro _ _ _ _ _; exact ⟨fun _ h => (by cases h), fun h => (by cases h)⟩
  | @iteTOk x t e m m' c hx _ iht =>
    intro s g hs hc hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    refine ⟨?_, fun h => (by cases h)⟩
    rintro m'' he; cases he
    rw [run.eq_5, stepI_jz, blt_false (by omega)]
    subst hs
    simp only [absS_regs, absS_mem] at *
    simp only [Bool.cond_false, hx, ↓reduceIte, nbeq_false hx, Bool.cond_false]
    obtain ⟨s2, g2, e2, a2, f2, l2⟩ := (iht hok.1 { s with fuel := s.fuel - 1, pc := s.pc + 1 } g rfl
      (by simp; omega) (by omega)).1 m' rfl
    rcases hr : run p inp deployedRO g t { s with fuel := s.fuel - 1, pc := s.pc + 1 } with ⟨y, hy⟩
    rw [hr] at e2; simp only at e2; subst e2
    obtain ⟨g3, rfl⟩ : ∃ g', g2 = g' + 1 := ⟨g2 - 1, by omega⟩
    simp only
    rw [stepI_jmp, blt_false (by simp at f2; omega)]
    simp only [Bool.cond_false]
    refine ⟨_, _, rfl, a2, ?_, by omega⟩
    simp at f2 ⊢; omega
  | @iteTHalt x t e m acc c hx _ iht =>
    intro s g hs hc hg
    refine ⟨fun _ h => (by cases h), fun he => ?_⟩
    cases he
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [run.eq_5, stepI_jz, blt_false (by omega)]
    subst hs
    simp only [absS_regs, absS_mem] at *
    simp only [Bool.cond_false, hx, ↓reduceIte, nbeq_false hx, Bool.cond_false]
    obtain ⟨s2, e2⟩ := (iht hok.1 { s with fuel := s.fuel - 1, pc := s.pc + 1 } g rfl
      (by simp; omega) (by omega)).2 (by trivial)
    rcases hr : run p inp deployedRO g t { s with fuel := s.fuel - 1, pc := s.pc + 1 } with ⟨y, hy⟩
    rw [hr] at e2; simp only at e2; subst e2
    exact ⟨s2, rfl⟩
  | iteTTrap => intro _ _ _ _ _; exact ⟨fun _ h => (by cases h), fun h => (by cases h)⟩
  | @iteF x t e m r c hx _ ihe =>
    intro s g hs hc hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [run.eq_5, stepI_jz, blt_false (by omega)]
    subst hs
    simp only [absS_regs, absS_mem] at *
    simp only [Bool.cond_false, hx, ↓reduceIte, nbeq_true hx, Bool.cond_true]
    have := ihe hok.2 { s with fuel := s.fuel - 1, pc := s.pc + t.size + 2 } g rfl (by simp; omega)
      (by omega)
    obtain ⟨h1, h2⟩ := this
    refine ⟨fun m' he => ?_, h2⟩
    obtain ⟨s', g', e', a', f', l'⟩ := h1 m' he
    exact ⟨s', g', e', a', by simp at f'; omega, by omega⟩
  | @loopExit x b m hx =>
    intro s g hs hc hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    refine ⟨?_, fun h => (by cases h)⟩
    rintro m' he; cases he
    rw [run.eq_6, stepI_jz, blt_false (by omega)]
    subst hs
    simp only [absS_regs, absS_mem] at *
    simp only [Bool.cond_false, hx, ↓reduceIte]
    exact ⟨_, _, rfl, rfl, rfl, by omega⟩
  | @loopHalt x b m acc c hx _ ihb =>
    intro s g hs hc hg
    refine ⟨fun _ h => (by cases h), fun he => ?_⟩
    cases he
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [run.eq_6, stepI_jz, blt_false (by omega)]
    subst hs
    simp only [absS_regs, absS_mem] at *
    simp only [Bool.cond_false, hx, ↓reduceIte, nbeq_false hx, Bool.cond_false]
    obtain ⟨s2, e2⟩ := (ihb hok { s with fuel := s.fuel - 1, pc := s.pc + 1 } g rfl
      (by simp; omega) (by omega)).2 (by trivial)
    rcases hr : run p inp deployedRO g b { s with fuel := s.fuel - 1, pc := s.pc + 1 } with ⟨y, hy⟩
    rw [hr] at e2; simp only at e2; subst e2
    exact ⟨s2, rfl⟩
  | loopTrap => intro _ _ _ _ _; exact ⟨fun _ h => (by cases h), fun h => (by cases h)⟩
  | @loopIter x b m m1 r c1 c2 hx _ _ ihb ihl =>
    intro s g hs hc hg
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [run.eq_6, stepI_jz, blt_false (by omega)]
    subst hs
    simp only [absS_regs, absS_mem] at *
    simp only [Bool.cond_false, hx, ↓reduceIte, nbeq_false hx, Bool.cond_false]
    obtain ⟨s2, g2, e2, a2, f2, l2⟩ := (ihb hok { s with fuel := s.fuel - 1, pc := s.pc + 1 } g rfl
      (by simp; omega) (by omega)).1 m1 rfl
    rcases hr : run p inp deployedRO g b { s with fuel := s.fuel - 1, pc := s.pc + 1 } with ⟨y, hy⟩
    rw [hr] at e2; simp only at e2; subst e2
    obtain ⟨g3, rfl⟩ : ∃ g', g2 = g' + 1 := ⟨g2 - 1, by omega⟩
    simp only
    rw [stepI_jmp, blt_false (by simp at f2; omega)]
    simp only [Bool.cond_false]
    have hl := ihl hok { s2 with fuel := s2.fuel - 1, pc := s.pc } g3 a2 (by simp at f2 ⊢; omega)
      (by omega)
    obtain ⟨h1, h2⟩ := hl
    refine ⟨fun m' he => ?_, h2⟩
    obtain ⟨s', g', e', a', f', l'⟩ := h1 m' he
    exact ⟨s', g', e', a', by simp at f2 f' ⊢; omega, by omega⟩
  | @halt x m =>
    intro s g hs hc hg
    refine ⟨fun _ h => (by cases h), fun he => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [run.eq_3]
    subst hs
    simp only [absS_regs, absS_mem] at *
    simp only [stepI, cost, exec1, blt_false (show ¬ s.fuel < 1 by omega), Bool.cond_false]
    have : s.regs x ≠ 0 := by
      intro h0; simp [absS, h0] at he
    simp [nbeq_false this]

/-! ## Whole programs -/

/-- Initial abstract state of a program. -/
def M.init (prog : Program) : M := ⟨fun _ => 0, fun j => prog.data.getD j 0⟩

theorem exec_accept_sound (prog : Program) (st : Stmt) (hok : st.ok) (hcode : prog.code = st.compile 0)
    (fuel : Nat) (h : (exec prog inp deployedRO (fuel + 1) (init prog fuel ())).1 = .accept) :
    ∃ c, Ev prog inp st (M.init prog) (.halt true) c := by
  rw [exec_program prog st (Stmt.ok_wf hok) hcode] at h
  have hs := run_sound (p := prog) (inp := inp) (fuel + 1) st (init prog fuel ()) hok
  have he := (exec_placed (p := prog) (inp := inp) (H := deployedRO) st (Stmt.ok_wf hok) (fuel + 1)
    (init prog fuel ()) (by intro i _; simp [init, hcode])).2
  revert h hs he
  rcases run prog inp deployedRO (fuel + 1) st (init prog fuel ()) with ⟨r, _⟩
  cases r with
  | cont s' g' =>
    intro h _ he
    have hpc : s'.pc = st.size := by simpa [init] using he s' g' rfl
    simp only [after] at h
    cases g' with
    | zero => simp [exec] at h
    | succ g =>
      rw [exec_succ'] at h
      have : prog.code[s'.pc]? = none := by
        rw [hpc, hcode]; simp [Stmt.compile_length]
      simp [step, this] at h
  | stop o s' =>
    intro h hs _
    simp only [after] at h
    subst h
    exact hs

theorem exec_accept_complete (prog : Program) (st : Stmt) (hok : st.ok)
    (hcode : prog.code = st.compile 0) (fuel c : Nat)
    (h : Ev prog inp st (M.init prog) (.halt true) c) (hc : c ≤ fuel) :
    (exec prog inp deployedRO (fuel + 1) (init prog fuel ())).1 = .accept := by
  rw [exec_program prog st (Stmt.ok_wf hok) hcode]
  obtain ⟨s', e⟩ := (run_complete h hok (init prog fuel ()) (fuel + 1) rfl (by simp [init]; omega)
    (by omega)).2 rfl
  revert e
  rcases run prog inp deployedRO (fuel + 1) st (init prog fuel ()) with ⟨r, _⟩
  intro e; simp only at e; subst e
  rfl

end NpaiIR
