import NpaiIR.Hoare

/-!
# NpaiIR.Lib.Base — conventions and basic macros

Conventions used by every library macro:

* `r15` always holds `1` and `r14` always holds `8` (`Kinv`). Programs set
  them once (`setupK`) and no macro writes them.
* A macro documents the registers it may write (its *clobber list*); every
  other register is preserved (`Frame`).
* Failures *trap* (`fail`): a trap is never acceptance, so a verifier is a
  straight sequence of checks that ends in `halt 15`.
-/

namespace NpaiIR

open ArenaCore Interp


def Kinv (m : M) : Prop := m.regs K1 = 1 ∧ m.regs K8 = 8

/-- Registers outside `C` are unchanged. -/
def Frame (C : List Nat) (m m' : M) : Prop := ∀ j, j ∉ C → m'.regs j = m.regs j

theorem Frame.refl (C : List Nat) (m : M) : Frame C m m := fun _ _ => rfl

theorem Frame.trans {C D : List Nat} {m1 m2 m3 : M} (h1 : Frame C m1 m2) (h2 : Frame D m2 m3) :
    Frame (C ++ D) m1 m3 := fun j hj => by
  rw [h2 j (fun h => hj (List.mem_append_right _ h)), h1 j (fun h => hj (List.mem_append_left _ h))]

theorem Frame.mono {C D : List Nat} {m m' : M} (h : Frame C m m') (hs : ∀ j ∈ C, j ∈ D) :
    Frame D m m' := fun j hj => h j (fun h' => hj (hs j h'))

theorem Frame.kinv {C : List Nat} {m m' : M} (h : Frame C m m') (h1 : K1 ∉ C) (h8 : K8 ∉ C)
    (hk : Kinv m) : Kinv m' := ⟨by rw [h K1 h1]; exact hk.1, by rw [h K8 h8]; exact hk.2⟩

variable {p : Program} {inp : Inputs}

theorem sound_of_total {X : Stmt} {m : M} {Q : M → Prop}
    (h : ∃ m' c, Ev p inp X m (.ok m') c ∧ Q m') {m'' : M} {c'' : Nat}
    (h' : Ev p inp X m (.ok m'') c'') : Q m'' := by
  obtain ⟨m', c, h1, h2⟩ := h
  obtain ⟨e, -⟩ := Ev.det h1 h'
  cases e; exact h2

/-! ## Basic statements -/

def nop : Stmt := .op (.mov 0 0)

/-- Trap unconditionally (load from address `2^32 - 1 ≥ memSize`). -/
def fail : Stmt := .seq (.op (.const 13 4294967295)) (.op (.ld8 13 13))

/-- Continue iff `r ≠ 0`, else trap. -/
def assert (r : Nat) : Stmt := .ite r nop fail

theorem ev_nop {m : M} : Ev p inp nop m (.ok m) 1 := by
  have h := @Ev.op p inp (.mov 0 0) m m rfl (mov00 m)
  simpa [cost, nop] using h

theorem ev_nop_iff {m m' : M} {c : Nat} : Ev p inp nop m (.ok m') c ↔ m' = m ∧ c = 1 := by
  constructor
  · intro h; obtain ⟨e, h2⟩ := Ev.det h ev_nop; cases e; exact ⟨rfl, h2⟩
  · rintro ⟨rfl, rfl⟩; exact ev_nop

theorem fail_no_ok (hp : p.memSize ≤ 4294967295) {m m' : M} {c : Nat} :
    ¬ Ev p inp fail m (.ok m') c := by
  intro h
  rw [fail, ev_seq_ok] at h
  obtain ⟨m1, c1, c2, h1, h2, -⟩ := h
  rw [ev_op_ok] at h1 h2
  obtain ⟨-, h1, -⟩ := h1
  obtain ⟨-, h2, -⟩ := h2
  simp only [ins, Option.some.injEq] at h1
  subst h1
  simp [ins, setReg, wordMod] at h2
  omega

theorem assert_sound (hp : p.memSize ≤ 4294967295) {r : Nat} {m m' : M} {c : Nat}
    (h : Ev p inp (assert r) m (.ok m') c) : m.regs r ≠ 0 ∧ m' = m ∧ c = 3 := by
  rcases ev_ite_ok.mp h with ⟨hx, c', h1, rfl⟩ | ⟨hx, c', h1, rfl⟩
  · rw [ev_nop_iff] at h1; exact ⟨hx, h1.1, by omega⟩
  · exact absurd h1 (fail_no_ok hp)

theorem assert_complete {r : Nat} {m : M} (h : m.regs r ≠ 0) :
    Ev p inp (assert r) m (.ok m) 3 := .iteTOk h ev_nop

/-! ## Sequencing helpers -/

/-- Right-nested sequence of statements. -/
def seqs : List Stmt → Stmt
  | [] => nop
  | [s] => s
  | s :: ss => .seq s (seqs ss)


end NpaiIR

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-- Continue iff `r = 0`, else trap. -/
def assertZ (r : Nat) : Stmt := .ite r fail nop

theorem assertZ_sound (hp : p.memSize ≤ 4294967295) {r : Nat} {m m' : M} {c : Nat}
    (h : Ev p inp (assertZ r) m (.ok m') c) : m.regs r = 0 ∧ m' = m ∧ c = 2 := by
  rcases ev_ite_ok.mp h with ⟨hx, c', h1, rfl⟩ | ⟨hx, c', h1, rfl⟩
  · exact absurd h1 (fail_no_ok hp)
  · rw [ev_nop_iff] at h1; exact ⟨hx, h1.1, by omega⟩

theorem assertZ_complete {r : Nat} {m : M} (h : m.regs r = 0) :
    Ev p inp (assertZ r) m (.ok m) 2 := .iteF h ev_nop

theorem assert_ok (r : Nat) : (assert r).ok := by simp [assert, Stmt.ok, nop, fail, okInstr]
theorem assertZ_ok (r : Nat) : (assertZ r).ok := by simp [assertZ, Stmt.ok, nop, fail, okInstr]
theorem assert_noHalt (r : Nat) : (assert r).noHalt := by simp [assert, Stmt.noHalt, nop, fail]
theorem assertZ_noHalt (r : Nat) : (assertZ r).noHalt := by simp [assertZ, Stmt.noHalt, nop, fail]

/-- `t := (a < b)`; continue iff it holds. -/
def chkLt (a b t : Nat) : Stmt := .seq (.op (.bin .ltu t a b)) (assert t)
/-- Continue iff `regs a ≤ regs b` (computed as `¬ b < a`). -/
def chkLe (a b t : Nat) : Stmt := .seq (.op (.bin .ltu t b a)) (assertZ t)
/-- Continue iff `regs a = regs b`. -/
def chkEq (a b t : Nat) : Stmt := .seq (.op (.bin .eq t a b)) (assert t)

theorem chkLt_spec (hp : p.memSize ≤ 4294967295) {a b t : Nat} {m m' : M} {c : Nat} :
    Ev p inp (chkLt a b t) m (.ok m') c ↔
      m.regs a < m.regs b ∧ m' = { m with regs := setReg m.regs t 1 } ∧ c = 4 := by
  constructor
  · intro h
    rw [chkLt, ev_seq_ok] at h
    obtain ⟨m1, c1, c2, h1, h2, rfl⟩ := h
    rw [ev_op_ok] at h1
    obtain ⟨-, h1, rfl⟩ := h1
    simp only [ins, Option.some.injEq] at h1; subst h1
    obtain ⟨hx, rfl, rfl⟩ := assert_sound hp h2
    simp only [setReg_same, eval_ltu] at hx
    have : m.regs a < m.regs b := by
      by_cases h : m.regs a < m.regs b
      · exact h
      · simp [h] at hx
    refine ⟨this, ?_, rfl⟩
    simp [eval_ltu, this]
  · rintro ⟨h, rfl, rfl⟩
    have e1 : Ev p inp (.op (.bin .ltu t a b)) m (.ok { m with regs := setReg m.regs t 1 }) 1 :=
      Ev.op rfl (by simp [ins, eval_ltu, h])
    exact Ev.seqOk e1 (assert_complete (by simp))

theorem chkLe_spec (hp : p.memSize ≤ 4294967295) {a b t : Nat} {m m' : M} {c : Nat} :
    Ev p inp (chkLe a b t) m (.ok m') c ↔
      m.regs a ≤ m.regs b ∧ m' = { m with regs := setReg m.regs t 0 } ∧ c = 3 := by
  constructor
  · intro h
    rw [chkLe, ev_seq_ok] at h
    obtain ⟨m1, c1, c2, h1, h2, rfl⟩ := h
    rw [ev_op_ok] at h1
    obtain ⟨-, h1, rfl⟩ := h1
    simp only [ins, Option.some.injEq] at h1; subst h1
    obtain ⟨hx, rfl, rfl⟩ := assertZ_sound hp h2
    simp only [setReg_same, eval_ltu] at hx
    have : m.regs a ≤ m.regs b := by
      by_cases h : m.regs b < m.regs a
      · simp [h] at hx
      · omega
    refine ⟨this, ?_, rfl⟩
    simp [eval_ltu, Nat.not_lt.mpr this]
  · rintro ⟨h, rfl, rfl⟩
    have e1 : Ev p inp (.op (.bin .ltu t b a)) m (.ok { m with regs := setReg m.regs t 0 }) 1 :=
      Ev.op rfl (by simp [ins, eval_ltu, Nat.not_lt.mpr h])
    exact Ev.seqOk e1 (assertZ_complete (by simp))

theorem chkEq_spec (hp : p.memSize ≤ 4294967295) {a b t : Nat} {m m' : M} {c : Nat} :
    Ev p inp (chkEq a b t) m (.ok m') c ↔
      m.regs a = m.regs b ∧ m' = { m with regs := setReg m.regs t 1 } ∧ c = 4 := by
  constructor
  · intro h
    rw [chkEq, ev_seq_ok] at h
    obtain ⟨m1, c1, c2, h1, h2, rfl⟩ := h
    rw [ev_op_ok] at h1
    obtain ⟨-, h1, rfl⟩ := h1
    simp only [ins, Option.some.injEq] at h1; subst h1
    obtain ⟨hx, rfl, rfl⟩ := assert_sound hp h2
    simp only [setReg_same, eval_eq] at hx
    have : m.regs a = m.regs b := by
      by_cases h : m.regs a = m.regs b
      · exact h
      · simp [h] at hx
    refine ⟨this, ?_, rfl⟩
    simp [eval_eq, this]
  · rintro ⟨h, rfl, rfl⟩
    have e1 : Ev p inp (.op (.bin .eq t a b)) m (.ok { m with regs := setReg m.regs t 1 }) 1 :=
      Ev.op rfl (by simp [ins, eval_eq, h])
    exact Ev.seqOk e1 (assert_complete (by simp))

theorem chkLt_ok (a b t : Nat) : (chkLt a b t).ok := ⟨rfl, assert_ok t⟩
theorem chkLe_ok (a b t : Nat) : (chkLe a b t).ok := ⟨rfl, assertZ_ok t⟩
theorem chkEq_ok (a b t : Nat) : (chkEq a b t).ok := ⟨rfl, assert_ok t⟩

end NpaiIR
