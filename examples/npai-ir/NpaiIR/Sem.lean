import NpaiIR.Basic

/-!
# NpaiIR.Sem — a fuel-free big-step semantics for `Stmt`

`run` (Basic) is the gas-indexed semantics that the compiler-correctness
theorem talks about; it threads `pc`, fuel and gas exactly like the machine.
For proofs about *programs* that is too concrete. This file gives the
standard alternative:

* `M`: the part of the machine state programs compute with (registers and
  memory);
* `ins`: the effect of one non-control instruction on `M` (`none` = trap),
  mirroring `ArenaCore.Interp.exec1` (checked in `Adequacy.lean`);
* `Ev st m r c`: big-step evaluation of `st` from `m` with result `r`
  (normal exit, halt with accept/reject, trap), where `c` is the **exact fuel
  cost** the machine charges for the run, including the compiler-inserted
  jumps.

`Adequacy.lean` proves that `Ev` agrees with `run` (hence, through
`exec_placed`, with `ArenaCore.Interp.exec`) in both directions: machine
acceptance yields an `Ev` derivation, and an `Ev` derivation of cost `c ≤ fuel`
yields machine acceptance. Fuel never appears in `Ev` itself.
-/

namespace NpaiIR

open ArenaCore Interp

/-- Registers and memory. -/
structure M where
  regs : Nat → Nat
  mem : Nat → UInt8

/-- Result of a fragment. -/
inductive R where
  | ok (m : M)
  | halt (acc : Bool)
  | trap

/-- Instructions supported by the abstract semantics: straight-line and not
`OUT` (verifiers never write outputs). `ROHASH` is interpreted with the
deployed protocol hash. -/
def okInstr : Instr → Bool
  | .halt _ | .jmp _ | .jz _ _ | .jnz _ _ | .out _ _ _ => false
  | _ => true

/-- Effect of one straight-line instruction (mirrors `exec1`); `none` = trap. -/
def ins (p : Program) (inp : Inputs) (m : M) : Instr → Option M
  | .const a imm => some { m with regs := setReg m.regs a (imm % wordMod) }
  | .mov a b => some { m with regs := setReg m.regs a (m.regs b) }
  | .bin op a b c => some { m with regs := setReg m.regs a (op.eval (m.regs b) (m.regs c)) }
  | .addi a b imm => some { m with regs := setReg m.regs a ((m.regs b + imm) % wordMod) }
  | .tlen a t => some { m with regs := setReg m.regs a ((inp.tape t).length % wordMod) }
  | .tload a b t =>
      if m.regs b < (inp.tape t).length then
        some { m with regs := setReg m.regs a ((inp.tape t).getD (m.regs b) 0).toNat }
      else none
  | .tcopy a b c t =>
      if m.regs b + m.regs c ≤ (inp.tape t).length ∧ m.regs a + m.regs c ≤ p.memSize then
        some { m with mem := writeMem m.mem (m.regs a) (m.regs c) ((inp.tape t).drop (m.regs b)) }
      else none
  | .ld8 a b =>
      if m.regs b < p.memSize then some { m with regs := setReg m.regs a (m.mem (m.regs b)).toNat }
      else none
  | .st8 a b =>
      if m.regs a < p.memSize then
        some { m with mem := writeMem m.mem (m.regs a) 1 [UInt8.ofNat (m.regs b % 256)] }
      else none
  | .sha256 a b c =>
      if m.regs b + m.regs c ≤ p.memSize ∧ m.regs a + 32 ≤ p.memSize then
        some { m with mem := writeMem m.mem (m.regs a) 32 (sha256 (readMem m.mem (m.regs b) (m.regs c))) }
      else none
  | .rohash a b c =>
      if m.regs b + m.regs c ≤ p.memSize ∧ m.regs a + 32 ≤ p.memSize then
        let d := sha256 (roTag ++ readMem m.mem (m.regs b) (m.regs c))
        some { m with mem := writeMem m.mem (m.regs a) 32 d }
      else none
  | .memeq a b c d =>
      if m.regs b + m.regs d ≤ p.memSize ∧ m.regs c + m.regs d ≤ p.memSize then
        let v := if readMem m.mem (m.regs b) (m.regs d) = readMem m.mem (m.regs c) (m.regs d) then 1 else 0
        some { m with regs := setReg m.regs a v }
      else none
  | _ => none

/-- Every statement only uses supported instructions in `op`. -/
def Stmt.ok : Stmt → Prop
  | .op i => okInstr i = true
  | .seq a b => a.ok ∧ b.ok
  | .ite _ t e => t.ok ∧ e.ok
  | .loop _ b => b.ok
  | .halt _ => True

theorem Stmt.ok_wf : ∀ {st : Stmt}, st.ok → st.wf
  | .op i, h => by
    cases i <;> simp_all [Stmt.ok, Stmt.wf, okInstr, plain]
  | .seq _ _, h => ⟨Stmt.ok_wf h.1, Stmt.ok_wf h.2⟩
  | .ite _ _ _, h => ⟨Stmt.ok_wf h.1, Stmt.ok_wf h.2⟩
  | .loop _ b, h => (Stmt.ok_wf (st := b) h :)
  | .halt _, _ => trivial

/-- No `halt` inside: such a fragment never halts. -/
def Stmt.noHalt : Stmt → Prop
  | .op _ => True
  | .seq a b => a.noHalt ∧ b.noHalt
  | .ite _ t e => t.noHalt ∧ e.noHalt
  | .loop _ b => b.noHalt
  | .halt _ => False

/-- Big-step evaluation with exact fuel cost. -/
inductive Ev (p : Program) (inp : Inputs) : Stmt → M → R → Nat → Prop
  | op {i m m'} : okInstr i = true → ins p inp m i = some m' →
      Ev p inp (.op i) m (.ok m') (cost m.regs i)
  | opTrap {i m} : okInstr i = true → ins p inp m i = none →
      Ev p inp (.op i) m .trap (cost m.regs i)
  | seqOk {a b m m1 r c1 c2} : Ev p inp a m (.ok m1) c1 → Ev p inp b m1 r c2 →
      Ev p inp (.seq a b) m r (c1 + c2)
  | seqHalt {a b m acc c} : Ev p inp a m (.halt acc) c → Ev p inp (.seq a b) m (.halt acc) c
  | seqTrap {a b m c} : Ev p inp a m .trap c → Ev p inp (.seq a b) m .trap c
  | iteTOk {x t e m m' c} : m.regs x ≠ 0 → Ev p inp t m (.ok m') c →
      Ev p inp (.ite x t e) m (.ok m') (c + 2)
  | iteTHalt {x t e m acc c} : m.regs x ≠ 0 → Ev p inp t m (.halt acc) c →
      Ev p inp (.ite x t e) m (.halt acc) (c + 1)
  | iteTTrap {x t e m c} : m.regs x ≠ 0 → Ev p inp t m .trap c →
      Ev p inp (.ite x t e) m .trap (c + 1)
  | iteF {x t e m r c} : m.regs x = 0 → Ev p inp e m r c → Ev p inp (.ite x t e) m r (c + 1)
  | loopExit {x b m} : m.regs x = 0 → Ev p inp (.loop x b) m (.ok m) 1
  | loopHalt {x b m acc c} : m.regs x ≠ 0 → Ev p inp b m (.halt acc) c →
      Ev p inp (.loop x b) m (.halt acc) (c + 1)
  | loopTrap {x b m c} : m.regs x ≠ 0 → Ev p inp b m .trap c → Ev p inp (.loop x b) m .trap (c + 1)
  | loopIter {x b m m1 r c1 c2} : m.regs x ≠ 0 → Ev p inp b m (.ok m1) c1 →
      Ev p inp (.loop x b) m1 r c2 → Ev p inp (.loop x b) m r (c1 + 2 + c2)
  | halt {x m} : Ev p inp (.halt x) m (.halt (m.regs x != 0)) 1

variable {p : Program} {inp : Inputs}

/-! ## Determinism -/

theorem Ev.det {st : Stmt} {m : M} {r r' : R} {c c' : Nat} (h : Ev p inp st m r c)
    (h' : Ev p inp st m r' c') : r = r' ∧ c = c' := by
  induction h generalizing r' c' with
  | op hi hm => cases h' <;> simp_all
  | opTrap hi hm => cases h' <;> simp_all
  | seqOk _ _ iha ihb =>
    cases h' with
    | seqOk ha hb =>
      obtain ⟨e1, rfl⟩ := iha ha; cases e1
      obtain ⟨h1, rfl⟩ := ihb hb; exact ⟨h1, rfl⟩
    | seqHalt ha => cases (iha ha).1
    | seqTrap ha => cases (iha ha).1
  | seqHalt _ ih =>
    cases h' with
    | seqOk ha _ => cases (ih ha).1
    | seqHalt ha => exact ih ha
    | seqTrap ha => cases (ih ha).1
  | seqTrap _ ih =>
    cases h' with
    | seqOk ha _ => cases (ih ha).1
    | seqHalt ha => cases (ih ha).1
    | seqTrap ha => exact ih ha
  | iteTOk hx _ ih =>
    cases h' with
    | iteTOk _ ht => obtain ⟨h1, rfl⟩ := ih ht; exact ⟨h1, rfl⟩
    | iteTHalt _ ht => cases (ih ht).1
    | iteTTrap _ ht => cases (ih ht).1
    | iteF hz _ => exact absurd hz hx
  | iteTHalt hx _ ih =>
    cases h' with
    | iteTOk _ ht => cases (ih ht).1
    | iteTHalt _ ht => obtain ⟨h1, rfl⟩ := ih ht; exact ⟨h1, rfl⟩
    | iteTTrap _ ht => cases (ih ht).1
    | iteF hz _ => exact absurd hz hx
  | iteTTrap hx _ ih =>
    cases h' with
    | iteTOk _ ht => cases (ih ht).1
    | iteTHalt _ ht => cases (ih ht).1
    | iteTTrap _ ht => obtain ⟨-, rfl⟩ := ih ht; exact ⟨rfl, rfl⟩
    | iteF hz _ => exact absurd hz hx
  | iteF hx _ ih =>
    cases h' with
    | iteTOk hz _ => exact absurd hx hz
    | iteTHalt hz _ => exact absurd hx hz
    | iteTTrap hz _ => exact absurd hx hz
    | iteF _ he => obtain ⟨h1, rfl⟩ := ih he; exact ⟨h1, rfl⟩
  | loopExit hx =>
    cases h' with
    | loopExit _ => exact ⟨rfl, rfl⟩
    | loopHalt hz _ => exact absurd hx hz
    | loopTrap hz _ => exact absurd hx hz
    | loopIter hz _ _ => exact absurd hx hz
  | loopHalt hx _ ih =>
    cases h' with
    | loopExit hz => exact absurd hz hx
    | loopHalt _ hb => obtain ⟨h1, rfl⟩ := ih hb; exact ⟨h1, rfl⟩
    | loopTrap _ hb => cases (ih hb).1
    | loopIter _ hb _ => cases (ih hb).1
  | loopTrap hx _ ih =>
    cases h' with
    | loopExit hz => exact absurd hz hx
    | loopHalt _ hb => cases (ih hb).1
    | loopTrap _ hb => obtain ⟨-, rfl⟩ := ih hb; exact ⟨rfl, rfl⟩
    | loopIter _ hb _ => cases (ih hb).1
  | loopIter hx _ _ ihb ihl =>
    cases h' with
    | loopExit hz => exact absurd hz hx
    | loopHalt _ hb => cases (ihb hb).1
    | loopTrap _ hb => cases (ihb hb).1
    | loopIter _ hb hl =>
      obtain ⟨e1, rfl⟩ := ihb hb; cases e1
      obtain ⟨h1, rfl⟩ := ihl hl; exact ⟨h1, rfl⟩
  | halt => cases h'; exact ⟨rfl, rfl⟩

theorem Ev.noHalt {st : Stmt} (hs : st.noHalt) {m : M} {acc : Bool} {c : Nat} :
    ¬ Ev p inp st m (.halt acc) c := by
  intro h
  generalize hr : R.halt acc = r at h
  induction h with
  | op => cases hr
  | opTrap => cases hr
  | seqOk _ _ _ ihb => exact ihb hs.2 hr
  | seqHalt _ ih => exact ih hs.1 hr
  | seqTrap => cases hr
  | iteTOk => cases hr
  | iteTHalt _ _ ih => exact ih hs.1 hr
  | iteTTrap => cases hr
  | iteF _ _ ih => exact ih hs.2 hr
  | loopExit => cases hr
  | loopHalt _ _ ih => exact ih hs hr
  | loopTrap => cases hr
  | loopIter _ _ _ _ ihl => exact ihl hs hr
  | halt => exact hs

/-! ## Inversion lemmas for normal termination -/

theorem ev_op_ok {i : Instr} {m m' : M} {c : Nat} :
    Ev p inp (.op i) m (.ok m') c ↔ okInstr i = true ∧ ins p inp m i = some m' ∧ c = cost m.regs i := by
  constructor
  · intro h; cases h; exact ⟨by assumption, by assumption, rfl⟩
  · rintro ⟨h1, h2, rfl⟩; exact .op h1 h2

theorem ev_seq_ok {a b : Stmt} {m m' : M} {c : Nat} :
    Ev p inp (.seq a b) m (.ok m') c ↔
      ∃ m1 c1 c2, Ev p inp a m (.ok m1) c1 ∧ Ev p inp b m1 (.ok m') c2 ∧ c = c1 + c2 := by
  constructor
  · intro h; cases h; exact ⟨_, _, _, by assumption, by assumption, rfl⟩
  · rintro ⟨m1, c1, c2, h1, h2, rfl⟩; exact .seqOk h1 h2

theorem ev_ite_ok {x : Nat} {t e : Stmt} {m m' : M} {c : Nat} :
    Ev p inp (.ite x t e) m (.ok m') c ↔
      (m.regs x ≠ 0 ∧ ∃ c', Ev p inp t m (.ok m') c' ∧ c = c' + 2) ∨
      (m.regs x = 0 ∧ ∃ c', Ev p inp e m (.ok m') c' ∧ c = c' + 1) := by
  constructor
  · intro h; cases h
    · exact .inl ⟨by assumption, _, by assumption, rfl⟩
    · exact .inr ⟨by assumption, _, by assumption, rfl⟩
  · rintro (⟨hx, c', h, rfl⟩ | ⟨hx, c', h, rfl⟩)
    · exact .iteTOk hx h
    · exact .iteF hx h

/-! ## Straight-line blocks -/

/-- A straight-line block of instructions as a statement. -/
def block : List Instr → Stmt
  | [] => .op (.mov 0 0)
  | [i] => .op i
  | i :: is => .seq (.op i) (block is)

/-- Functional semantics of a block: final state and cost, `none` on trap. -/
def runSL (p : Program) (inp : Inputs) : List Instr → M → Option (M × Nat)
  | [], m => some (m, 1)
  | [i], m => (ins p inp m i).map fun m' => (m', cost m.regs i)
  | i :: j :: is, m =>
    match ins p inp m i with
    | none => none
    | some m' => (runSL p inp (j :: is) m').map fun (m'', c) => (m'', cost m.regs i + c)

def allOk (is : List Instr) : Prop := ∀ i ∈ is, okInstr i = true

theorem block_ok {is : List Instr} (h : allOk is) : (block is).ok := by
  induction is with
  | nil => simp [block, Stmt.ok, okInstr]
  | cons i is ih =>
    cases is with
    | nil => exact h i (by simp)
    | cons j js =>
      exact ⟨h i (by simp), ih fun k hk => h k (List.mem_cons_of_mem _ hk)⟩

theorem block_noHalt (is : List Instr) : (block is).noHalt := by
  induction is with
  | nil => trivial
  | cons i is ih => cases is with
    | nil => trivial
    | cons j js => exact ⟨trivial, ih⟩

theorem mov00 (m : M) : ins p inp m (.mov 0 0) = some m := by
  simp only [ins]
  congr
  funext j; simp [setReg]; intro h; subst h; rfl

/-- `Ev` on a block is exactly `runSL`. -/
theorem ev_block {is : List Instr} (h : allOk is) {m m' : M} {c : Nat} :
    Ev p inp (block is) m (.ok m') c ↔ runSL p inp is m = some (m', c) := by
  induction is generalizing m c with
  | nil =>
    simp only [block, runSL, ev_op_ok, mov00, Option.some.injEq]
    constructor
    · rintro ⟨-, rfl, rfl⟩; simp [cost]
    · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  | cons i is ih =>
    cases is with
    | nil =>
      simp only [block, runSL, ev_op_ok, Option.map_eq_some_iff]
      constructor
      · rintro ⟨-, h1, rfl⟩; exact ⟨m', h1, rfl⟩
      · rintro ⟨m'', h1, h2⟩; cases h2; exact ⟨h i (by simp), h1, rfl⟩
    | cons j js =>
      have hrest : allOk (j :: js) := fun k hk => h k (List.mem_cons_of_mem _ hk)
      simp only [block, runSL, ev_seq_ok, ev_op_ok]
      constructor
      · rintro ⟨m1, c1, c2, ⟨-, h1, rfl⟩, h2, rfl⟩
        rw [h1]; simp only [Option.map_eq_some_iff]
        exact ⟨(m', c2), (ih hrest).1 h2, rfl⟩
      · intro hr
        cases h1 : ins p inp m i with
        | none => rw [h1] at hr; cases hr
        | some m1 =>
          rw [h1] at hr
          simp only [Option.map_eq_some_iff] at hr
          obtain ⟨⟨m2, c2⟩, h2, he⟩ := hr
          cases he
          exact ⟨m1, _, c2, ⟨h i (by simp), by simp [h1], rfl⟩, (ih hrest).2 h2, rfl⟩

end NpaiIR

namespace NpaiIR
open ArenaCore Interp
variable {p : Program} {inp : Inputs}

theorem ev_block_of {is : List Instr} (h : allOk is) {m m' : M} {c : Nat}
    (hr : runSL p inp is m = some (m', c)) : Ev p inp (block is) m (.ok m') c := (ev_block h).2 hr

end NpaiIR
