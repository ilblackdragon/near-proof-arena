import NpaiIR.Hoare

/-!
# NpaiIR.Exe — a functional evaluator for loop-free code

`exe st m` runs a statement without loops or halts and returns the final
state and the exact cost (`none` = trap or unsupported). `ev_exe`: for
loop-free supported code, `Ev st m (.ok m') c ↔ exe st m = some (m', c)`, so
both directions of a specification can be obtained by evaluating `exe` with
`simp` (symbolic execution through `if`s on register values).
-/

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

def exe (p : Program) (inp : Inputs) : Stmt → M → Option (M × Nat)
  | .op i, m => if okInstr i = true then (ins p inp m i).map fun m' => (m', cost m.regs i) else none
  | .seq a b, m =>
    match exe p inp a m with
    | none => none
    | some (m1, c1) => (exe p inp b m1).map fun (m2, c2) => (m2, c1 + c2)
  | .ite x t e, m =>
    if m.regs x = 0 then (exe p inp e m).map fun (m', c) => (m', c + 1)
    else (exe p inp t m).map fun (m', c) => (m', c + 2)
  | .loop _ _, _ => none
  | .halt _, _ => none

/-- No loops and no halts. -/
def Stmt.loopFree : Stmt → Prop
  | .op _ => True
  | .seq a b => a.loopFree ∧ b.loopFree
  | .ite _ t e => t.loopFree ∧ e.loopFree
  | .loop _ _ => False
  | .halt _ => False

theorem exe_sound : ∀ {st : Stmt} {m m' : M} {c : Nat}, exe p inp st m = some (m', c) →
    Ev p inp st m (.ok m') c
  | .op i, m, m', c, h => by
    simp only [exe] at h
    split at h
    · rename_i hi
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨m'', h1, rfl, rfl⟩ := h
      exact .op hi h1
    · cases h
  | .seq a b, m, m', c, h => by
    simp only [exe] at h
    split at h
    · cases h
    · rename_i m1 c1 h1
      simp only [Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at h
      obtain ⟨m2, c2, h2, rfl, rfl⟩ := h
      exact .seqOk (exe_sound h1) (exe_sound h2)
  | .ite x t e, m, m', c, h => by
    simp only [exe] at h
    split at h
    · rename_i hx
      simp only [Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at h
      obtain ⟨m2, c2, h2, rfl, rfl⟩ := h
      exact .iteF hx (exe_sound h2)
    · rename_i hx
      simp only [Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists] at h
      obtain ⟨m2, c2, h2, rfl, rfl⟩ := h
      exact .iteTOk hx (exe_sound h2)
  | .loop _ _, _, _, _, h => by simp [exe] at h
  | .halt _, _, _, _, h => by simp [exe] at h

theorem exe_complete : ∀ {st : Stmt}, st.loopFree → ∀ {m m' : M} {c : Nat},
    Ev p inp st m (.ok m') c → exe p inp st m = some (m', c)
  | .op i, _, m, m', c, h => by
    rw [ev_op_ok] at h
    obtain ⟨hi, h1, rfl⟩ := h
    simp [exe, hi, h1]
  | .seq a b, hl, m, m', c, h => by
    rw [ev_seq_ok] at h
    obtain ⟨m1, c1, c2, h1, h2, rfl⟩ := h
    simp [exe, exe_complete hl.1 h1, exe_complete hl.2 h2]
  | .ite x t e, hl, m, m', c, h => by
    rcases ev_ite_ok.mp h with ⟨hx, c', h1, rfl⟩ | ⟨hx, c', h1, rfl⟩
    · simp [exe, hx, exe_complete hl.1 h1]
    · simp [exe, hx, exe_complete hl.2 h1]
  | .loop _ _, hl, _, _, _, _ => absurd hl id
  | .halt _, hl, _, _, _, _ => absurd hl id

theorem ev_exe {st : Stmt} (hl : st.loopFree) {m m' : M} {c : Nat} :
    Ev p inp st m (.ok m') c ↔ exe p inp st m = some (m', c) :=
  ⟨exe_complete hl, exe_sound⟩

/-- Sequencing a loop-free prefix: `exe` result then the rest. -/
theorem ev_seq_exe {a b : Stmt} (ha : a.loopFree) {m m' : M} {c : Nat} :
    Ev p inp (.seq a b) m (.ok m') c ↔
      ∃ m1 c1 c2, exe p inp a m = some (m1, c1) ∧ Ev p inp b m1 (.ok m') c2 ∧ c = c1 + c2 := by
  rw [ev_seq_ok]
  constructor
  · rintro ⟨m1, c1, c2, h1, h2, rfl⟩; exact ⟨m1, c1, c2, exe_complete ha h1, h2, rfl⟩
  · rintro ⟨m1, c1, c2, h1, h2, rfl⟩; exact ⟨m1, c1, c2, exe_sound h1, h2, rfl⟩

theorem exe_seq_of {a b : Stmt} {m m1 m2 : M} {c1 c2 : Nat} (h1 : exe p inp a m = some (m1, c1))
    (h2 : exe p inp b m1 = some (m2, c2)) : exe p inp (.seq a b) m = some (m2, c1 + c2) := by
  simp [exe, h1, h2]

end NpaiIR
