import ArenaCore.Interp

/-!
# ArenaCore.InterpLemmas — reasoning toolkit for NPAI programs

Lemmas for symbolic execution of bytecode in proofs (used by the Toy
certificate; available to candidates).  Nothing here changes the semantics.
-/

namespace ArenaCore
namespace Interp

variable {σ : Type}

/-- Continuation after one step. -/
def cont (p : Program) (inp : Inputs) (H : HashOracle σ) (g : Nat) :
    StepResult σ → Outcome × State σ
  | .next s' => exec p inp H g s'
  | .done o s' => (o, s')

@[simp] theorem cont_next (p : Program) (inp : Inputs) (H : HashOracle σ) (g : Nat)
    (s : State σ) : cont p inp H g (.next s) = exec p inp H g s := rfl

@[simp] theorem cont_done (p : Program) (inp : Inputs) (H : HashOracle σ) (g : Nat)
    (o : Outcome) (s : State σ) : cont p inp H g (.done o s) = (o, s) := rfl

theorem exec_succ (p : Program) (inp : Inputs) (H : HashOracle σ) (g : Nat) (s : State σ) :
    exec p inp H (g + 1) s = cont p inp H g (step p inp H s) := rfl

theorem cont_ite (p : Program) (inp : Inputs) (H : HashOracle σ) (g : Nat) (c : Prop)
    {_ : Decidable c} (a b : StepResult σ) :
    cont p inp H g (if c then a else b) = if c then cont p inp H g a else cont p inp H g b := by
  split <;> rfl

theorem fst_ite {α β : Type} (c : Prop) {_ : Decidable c} (a b : α × β) :
    (if c then a else b).1 = if c then a.1 else b.1 := by
  split <;> rfl

theorem ite_eq_accept (c : Prop) {_ : Decidable c} (a b : Outcome) :
    ((if c then a else b) = .accept) ↔ (c ∧ a = .accept) ∨ (¬ c ∧ b = .accept) := by
  split <;> simp_all

theorem cont_cond (p : Program) (inp : Inputs) (H : HashOracle σ) (g : Nat) (b : Bool)
    (x y : StepResult σ) :
    cont p inp H g (cond b x y) = cond b (cont p inp H g x) (cont p inp H g y) := by
  cases b <;> rfl

theorem fst_cond {α β : Type} (b : Bool) (x y : α × β) :
    (cond b x y).1 = cond b x.1 y.1 := by
  cases b <;> rfl

theorem cond_eq_accept (b : Bool) (x y : Outcome) :
    (cond b x y = .accept) ↔ (b = true ∧ x = .accept) ∨ (b = false ∧ y = .accept) := by
  cases b <;> simp

theorem run_eq_some_true_iff (p : Program) (inp : Inputs) (fuel : Nat) :
    run p inp fuel = some true ↔ (runFull p inp fuel).1 = .accept := by
  unfold run
  split <;> simp_all

/-! ## Boolean comparisons (for `simp (disch := omega)`) -/

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]
theorem ble_iff {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]
theorem nbeq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem bool_false_iff {x : Bool} {P : Prop} (h : x = true ↔ P) : x = false ↔ ¬ P := by
  cases x <;> simp_all

theorem blt_false_iff {a b : Nat} : Nat.blt a b = false ↔ ¬ a < b := bool_false_iff blt_iff
theorem ble_false_iff {a b : Nat} : Nat.ble a b = false ↔ ¬ a ≤ b := bool_false_iff ble_iff
theorem nbeq_false_iff {a b : Nat} : Nat.beq a b = false ↔ ¬ a = b := bool_false_iff nbeq_iff

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := blt_iff.mpr h
theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := blt_false_iff.mpr h
theorem ble_true {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := ble_iff.mpr h
theorem ble_false {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := ble_false_iff.mpr h
theorem nbeq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := nbeq_iff.mpr h
theorem nbeq_false {a b : Nat} (h : ¬ a = b) : Nat.beq a b = false := nbeq_false_iff.mpr h

/-! ## Memory -/

@[simp] theorem readMem_length (m : Nat → UInt8) (p n : Nat) : (readMem m p n).length = n := by
  simp [readMem]

theorem readMem_congr {m m' : Nat → UInt8} {p n : Nat} (h : ∀ i, i < n → m (p + i) = m' (p + i)) :
    readMem m p n = readMem m' p n := by
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [readMem_length] at h1
  simp [readMem, h i h1]

/-- Reading back exactly what was written. -/
theorem readMem_writeMem_self (m : Nat → UInt8) (d len : Nat) (src : Bytes)
    (h : len ≤ src.length) : readMem (writeMem m d len src) d len = src.take len := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [readMem_length] at h1
  simp only [readMem, writeMem, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [ite_eq_left (by omega)]
  simp [Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < src.length)]

/-- Reading a range disjoint from a write. -/
theorem readMem_writeMem_disjoint (m : Nat → UInt8) (d len : Nat) (src : Bytes) (p n : Nat)
    (h : p + n ≤ d ∨ d + len ≤ p) : readMem (writeMem m d len src) p n = readMem m p n := by
  apply readMem_congr
  intro i hi
  simp only [writeMem]
  rw [ite_eq_right (by omega)]

theorem writeMem_apply_out (m : Nat → UInt8) (d len : Nat) (src : Bytes) (j : Nat)
    (h : j < d ∨ d + len ≤ j) : writeMem m d len src j = m j := by
  simp only [writeMem]
  rw [ite_eq_right (by omega)]

theorem writeMem_apply_in (m : Nat → UInt8) (d len : Nat) (src : Bytes) (j : Nat)
    (h1 : d ≤ j) (h2 : j < d + len) : writeMem m d len src j = src.getD (j - d) 0 := by
  simp only [writeMem]
  rw [ite_eq_left ⟨h1, h2⟩]

end Interp
end ArenaCore
