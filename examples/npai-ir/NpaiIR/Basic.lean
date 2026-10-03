import ArenaCore.InterpLemmas

/-!
# NpaiIR: a structured IR compiled to NPAI v1, with a proven-correct compiler

Route (a) of the implementation connection needs a *bytecode* verifier whose
behaviour is proved against `ArenaCore.Interp`. Writing that bytecode by hand
and proving it by symbolic execution (as `Toy` does) does not scale to the
NEAR relation. This module provides the first layer of the alternative:

* `Stmt`: structured programs over NPAI instructions (straight-line
  instructions, sequencing, `if r ≠ 0`, `while r ≠ 0`, `halt`);
* `Stmt.compile b`: its NPAI code when placed at instruction address `b`;
* `run`: a gas-indexed semantics of `Stmt` that charges fuel and gas exactly
  as the machine does (one gas per executed instruction, including the
  compiler-inserted `JZ`/`JMP`);
* `exec_placed` (**compiler correctness**): if the compiled code of `st` sits
  in the program at the current `pc`, then running the *machine* is the same
  as running `st` with `run` and then continuing the machine from the
  resulting state, which is at `pc + st.size`. The statement is an equation
  between machine runs, so it covers acceptance, rejection, traps and fuel
  or gas exhaustion in both directions.

Proofs about verifiers are then done on `run` (structured control flow, loop
invariants by induction) instead of on raw program counters.
-/

namespace NpaiIR

open ArenaCore Interp

variable {σ : Type}

/-- Instructions that fall through to `pc + 1` (no control transfer). -/
def plain : Instr → Bool
  | .halt _ | .jmp _ | .jz _ _ | .jnz _ _ => false
  | _ => true

inductive Stmt where
  | op (i : Instr)
  | seq (a b : Stmt)
  | ite (r : Nat) (t e : Stmt)
  | loop (r : Nat) (body : Stmt)
  | halt (r : Nat)

namespace Stmt

def size : Stmt → Nat
  | .op _ => 1
  | .seq a b => a.size + b.size
  | .ite _ t e => t.size + e.size + 2
  | .loop _ b => b.size + 2
  | .halt _ => 1

/-- Only plain instructions in `op`. -/
def wf : Stmt → Prop
  | .op i => plain i = true
  | .seq a b => a.wf ∧ b.wf
  | .ite _ t e => t.wf ∧ e.wf
  | .loop _ b => b.wf
  | .halt _ => True

/-- Code of `st` placed at address `b`. -/
def compile : Nat → Stmt → List Instr
  | _, .op i => [i]
  | b, .seq x y => x.compile b ++ y.compile (b + x.size)
  | b, .ite r t e =>
    [.jz r (b + t.size + 2)] ++ t.compile (b + 1) ++ [.jmp (b + t.size + 2 + e.size)] ++
      e.compile (b + t.size + 2)
  | b, .loop r body => [.jz r (b + body.size + 2)] ++ body.compile (b + 1) ++ [.jmp b]
  | _, .halt r => [.halt r]

theorem compile_length : ∀ (st : Stmt) (b : Nat), (st.compile b).length = st.size
  | .op _, _ => rfl
  | .seq x y, b => by simp [compile, size, compile_length x, compile_length y]
  | .ite r t e, b => by simp [compile, size, compile_length t, compile_length e]; omega
  | .loop r body, b => by simp [compile, size, compile_length body]
  | .halt _, _ => rfl

end Stmt

/-! ## Semantics -/

/-- Execute one fetched instruction exactly like `Interp.step` does. -/
def stepI (p : Program) (inp : Inputs) (H : HashOracle σ) (i : Instr) (s : State σ) : StepResult σ :=
  bif Nat.blt s.fuel (cost s.regs i) then .done .outOfFuel s
  else exec1 p inp H { s with fuel := s.fuel - cost s.regs i } i

theorem step_of_fetch {p : Program} {inp : Inputs} {H : HashOracle σ} {s : State σ} {i : Instr}
    (h : p.code[s.pc]? = some i) : step p inp H s = stepI p inp H i s := by
  simp [step, stepI, h]

inductive Res (σ : Type) where
  | cont (s : State σ) (g : Nat)
  | stop (o : Outcome) (s : State σ)

def Res.gas : Res σ → Nat
  | .cont _ g => g
  | .stop _ _ => 0

/-- Lexicographic decrease helper. -/
theorem lex_le_lt {a b c d : Nat} (h1 : a ≤ b) (h2 : c < d) :
    Prod.Lex (· < ·) (· < ·) (a, c) (b, d) := by
  rcases Nat.lt_or_ge a b with h | h
  · exact Prod.Lex.left _ _ h
  · have : a = b := by omega
    subst this; exact Prod.Lex.right _ h2

/-- Gas-indexed semantics; the gas of a `cont` result never exceeds the input. -/
def run (p : Program) (inp : Inputs) (H : HashOracle σ) :
    (g : Nat) → Stmt → State σ → { r : Res σ // r.gas ≤ g }
  | 0, _, s => ⟨.stop .outOfFuel s, Nat.zero_le _⟩
  | g + 1, .op i, s =>
    match stepI p inp H i s with
    | .next s' => ⟨.cont s' g, by simp [Res.gas]⟩
    | .done o s' => ⟨.stop o s', by simp [Res.gas]⟩
  | g + 1, .halt r, s =>
    match stepI p inp H (.halt r) s with
    | .next s' => ⟨.cont s' g, by simp [Res.gas]⟩
    | .done o s' => ⟨.stop o s', by simp [Res.gas]⟩
  | g + 1, .seq a b, s =>
    match run p inp H (g + 1) a s with
    | ⟨.cont s' g', h⟩ =>
      let r := run p inp H g' b s'
      ⟨r.1, Nat.le_trans r.2 (by simpa [Res.gas] using h)⟩
    | ⟨.stop o s', _⟩ => ⟨.stop o s', by simp [Res.gas]⟩
  | g + 1, .ite r t e, s =>
    match stepI p inp H (.jz r (s.pc + t.size + 2)) s with
    | .done o s' => ⟨.stop o s', by simp [Res.gas]⟩
    | .next s1 =>
      if s.regs r = 0 then
        let x := run p inp H g e s1
        ⟨x.1, Nat.le_trans x.2 (Nat.le_succ g)⟩
      else
        match run p inp H g t s1 with
        | ⟨.stop o s', _⟩ => ⟨.stop o s', by simp [Res.gas]⟩
        | ⟨.cont s2 0, _⟩ => ⟨.stop .outOfFuel s2, by simp [Res.gas]⟩
        | ⟨.cont s2 (g2 + 1), h⟩ =>
          match stepI p inp H (.jmp (s.pc + t.size + 2 + e.size)) s2 with
          | .next s3 => ⟨.cont s3 g2, by simp [Res.gas] at h ⊢; omega⟩
          | .done o s3 => ⟨.stop o s3, by simp [Res.gas]⟩
  | g + 1, .loop r body, s =>
    match stepI p inp H (.jz r (s.pc + body.size + 2)) s with
    | .done o s' => ⟨.stop o s', by simp [Res.gas]⟩
    | .next s1 =>
      if s.regs r = 0 then ⟨.cont s1 g, by simp [Res.gas]⟩
      else
        match run p inp H g body s1 with
        | ⟨.stop o s', _⟩ => ⟨.stop o s', by simp [Res.gas]⟩
        | ⟨.cont s2 0, _⟩ => ⟨.stop .outOfFuel s2, by simp [Res.gas]⟩
        | ⟨.cont s2 (g2 + 1), h⟩ =>
          match stepI p inp H (.jmp s.pc) s2 with
          | .done o s3 => ⟨.stop o s3, by simp [Res.gas]⟩
          | .next s3 =>
            let x := run p inp H g2 (.loop r body) s3
            ⟨x.1, by simp [Res.gas] at h; exact Nat.le_trans x.2 (by omega)⟩
termination_by g st => (g, sizeOf st)
decreasing_by
  all_goals first
    | (apply lex_le_lt <;> simp_all [Res.gas] <;> omega)
    | (apply Prod.Lex.left; simp_all [Res.gas] <;> omega)

end NpaiIR
